#!/usr/bin/env python3
r"""Query the theory index — computed live from .thy files on every invocation.

All commands re-parse the theory tree (<100ms).  Results are always in
sync with the current .thy source.  Use -h/--help on any subcommand for
its options.

File organisation (section banners below mark each):

* **Parsing** — `Entry` / `TheorySection` / `CallGraph` dataclasses,
  ROOT walking, .thy parsing, span attribution.
* **Call graph and shared filter helpers** —
  `_noise_ranges` / `_build_def_sites` provide the per-theory
  exclusion ranges (prose text blocks; definition-site spans) shared by
  single-name search (`_find_callers`) and bulk graph construction
  (`_build_call_graph`).  `_bfs_depths` is the single BFS behind every
  `-r` form (`callers`/`callees` over the call graph, `deps`/`uses` over
  imports).

  Two forward/reverse pairs, at different granularities: entry-level
  `callees` (forward) / `callers` (reverse) over proof-body references;
  theory-level `deps` (forward) / `uses` (reverse) over imports.
  `_scan_methods` is the router's complement: the `PROOF_METHODS` tokens
  `_is_citation_name` rejects as fact edges are the method uses it tallies
  for the `methods` query.
* **Rendering** — `_format_extent`, `render_entry`, preview/comment
  formatting.
* **Verbosity-mode dispatch** — the `-c`/`--names`/`-a`/`-V` resolution shared
  across subcommands.
* **Commands** — one `cmd_*` function per subcommand.  Output discipline:
  `-c` prints a bare integer (no decoration); verbose forms print
  hits + footers.
* **Argument parsing** — argparse subparsers.  Shared flag helpers
  (`_add_count_flag`, `_add_names_flag`, `_add_with_comments_flag`,
  `_add_path_files_arg`, `_add_mode_flags`, `_add_verbatim_flag`,
  `_add_statement_flag`, `_add_comment_flags`, `_add_context_flag`) keep
  per-subparser declarations short and uniform.
"""

from __future__ import annotations

import re
import sys
from bisect import bisect_right
from collections import Counter
from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from operator import itemgetter
from pathlib import Path

from isabelle_query import _isabelle_namespace as _isa_ns
from isabelle_query.common import (
    default_t_dir,
    discover_roots,
    parse_root_sessions,
    parse_thy_imports,
    resolve_session_theory,
)

# ---------------------------------------------------------------------------
# Parsing — walks ROOT files and extracts entries from .thy sources
# ---------------------------------------------------------------------------

@dataclass
class Entry:
    tag: str            # DEF, FUN, LEMMA, THEOREM, DATATYPE, TYPE, RECORD, AXIOM
    name: str           # identifier
    text: str           # legacy pre-formatted text (for `theory` dump)
    theory: str = ""
    thy_line: int = 0       # 1-indexed start line in the .thy source file
    decl_end_line: int = 0  # 1-indexed last line of the declaration
                            # (last header line before proof / blank / next decl)
    proof_line: int = 0     # 1-indexed first line of the proof (0 if no proof)
    thy_end: int = 0        # 1-indexed end of this entry's span: the line
                            # before the *next* entry's src_start (its leading
                            # `text` preamble, if any, else its declaration) or
                            # the next section.  Includes this entry's trailing
                            # blank lines but NOT the following entry's leading
                            # doc block — that block documents, and belongs to,
                            # the following entry (see src_start).  For a safe
                            # relocation cut use body_end_line (which also drops
                            # the trailing blanks).
    body_end_line: int = 0  # 1-indexed last line that belongs to this entry's
                            # body (the closing `qed`, the terminating `by` /
                            # `.`, or for declarations the last header line).
                            # Stops before any trailing inter-lemma `text` /
                            # `\<comment>` block.  Safe cut boundary for
                            # `bin/move-block.py`.
    # Comment context attached during _parse_one:
    preamble: tuple[int, int] | None = None
        # (start, end) of the `text \<open>...\<close>` block immediately
        # preceding this entry, if one exists within ~3 blank lines.
    roadmap: list[tuple[int, str]] = field(default_factory=list)
        # (line_no, content) for `\<comment> \<open>...\<close>` annotations
        # found inside this entry's proof body.
    conjuncts: list[str] = field(default_factory=list)
        # Named conjuncts of a multi-`shows` lemma (e.g. mttm_step_src's
        # mttm_step_src_neq_t).  Each is a citable fact that resolves to
        # this entry under show / find / callers / callees, but is not a
        # separate Entry (so it never inflates counts or splits call-graph
        # attribution — resolution happens at the command boundary).

    @property
    def src_start(self) -> int:
        """First line of this entry's span: the leading `text` preamble's
        start if one is attached, else the declaration line.  The preamble
        documents THIS entry, so it counts as part of this entry's extent
        (and is excluded from the preceding entry's `thy_end`)."""
        return self.preamble[0] if self.preamble else self.thy_line

    @property
    def line_count(self) -> int:
        """Inclusive source-span length [src_start..thy_end]; 0 if unplaced."""
        return self.thy_end - self.src_start + 1 if self.thy_line > 0 else 0


@dataclass
class TheorySection:
    theory: str
    path: Path
    entries: list[Entry]
    thy_lines: int = 0
    outline: list[tuple[str, str, int]] = field(default_factory=list)
    text_blocks: list[tuple[int, int]] = field(default_factory=list)
        # All top-level text blocks in the theory, used for `outline` rendering
        # (per-entry preambles are stored on Entry.preamble).
    comment_ranges: list[tuple[int, int]] = field(default_factory=list)
        # Multi-line ranges for `\<comment> \<open>...\<close>` annotations;
        # folded into `_noise_spans`, so every search/scan (grep, methods, the
        # call graph, proof-block drill-down) skips them as non-live source.
        # (Distinct from comment_lines, which records first-line content for the
        # roadmap-attachment feature.)
    is_thy: bool = True
        # False for a non-`.thy` path passed as a trailing grep positional
        # (e.g. `query grep PAT notes.md`).  Such a section is parsed
        # *plainly* (no entries, outline, text/comment blocks): the Isabelle
        # entry-grammar does not apply to Markdown / prose, so cmd_grep treats
        # it as plain `grep` — every matched line, no synthesised owning-entry
        # label, no live/comment classification.
    line_window: tuple[int, int | None] | None = None
        # Optional inclusive 1-indexed [lo, hi] line window from a grep
        # `PATH:A..B` positional, set by `_load_sections(windows=True)`.
        # `_grep_sections` skips lines outside it; commands that don't read
        # it (largest/sorry) never see a window (the suffix isn't parsed for
        # them, so `largest Foo:1..9` errors rather than silently ignoring).
    _source_cache: list[str] | None = None

    def source(self) -> list[str]:
        if self._source_cache is None:
            self._source_cache = self.path.read_text().splitlines()
        return self._source_cache

    def slice(self, start: int, end: int) -> list[str]:
        """Return 1-indexed inclusive line range from the .thy source."""
        lines = self.source()
        s = max(0, start - 1)
        e = min(len(lines), end)
        return lines[s:e]


@dataclass
class CallGraph:
    """Name-level dependency graph built by a single pass over all sources."""
    callers: dict[str, set[str]]   # callee_name → {caller entry names}
    callees: dict[str, set[str]]   # caller_name → {callee names referenced}
    all_names: set[str]            # universe of indexed entry names


# `(?=\s|$)` (a token boundary), not a consumed `\s`, so a keyword standing
# ALONE on its line — the "name on a following line" form — still matches.
# It stays a whole-word test (`definitions`/`inductively` do not match), and
# being zero-width it leaves the `line[len(keyword):]` slicing untouched.
DECL_RE = re.compile(
    r"^(definition|abbreviation|function|fun|primrec|inductive_set|inductive|lemma|corollary|theorem|axiomatization|datatype|type_synonym|record)(?=\s|$)"
)

TAG_MAP = {
    "definition": "DEF", "abbreviation": "ABBREV",
    "function": "FUN", "fun": "FUN", "primrec": "FUN",
    "inductive_set": "INDSET", "inductive": "IND",
    "lemma": "LEMMA", "corollary": "LEMMA",
    "theorem": "THEOREM",
    "axiomatization": "AXIOM",
    "datatype": "DATATYPE", "type_synonym": "TYPE", "record": "RECORD",
}

# Tag families shared across commands.  Named so the membership lists can't
# drift between call sites: definition-like exports vs the citation-graph-
# eligible kinds (the two sets genuinely differ — datatypes/records/types are
# definitions but never call-graph nodes; lemmas/theorems are the reverse).
_DEFINITION_TAGS = frozenset(
    {"DEF", "ABBREV", "FUN", "DATATYPE", "RECORD", "TYPE"})
_CITABLE_TAGS = frozenset({"LEMMA", "THEOREM", "FUN", "DEF", "ABBREV"})

# --- Custom outer-syntax commands (faithful keyword-table scan) ------------
# An AFP entry may define its own theory commands (AOT's `AOT_theorem`,
# `AOT_define`, ...) through Isabelle's command framework.  The one fact the
# regex parser cannot otherwise know — that `AOT_theorem` is a theorem-like
# command — is declared as PLAIN TEXT in a theory header, and that declaration
# *is* Isabelle's keyword table (Pure/Thy/thy_header.ML parses exactly the
# `keywords "name" :: kind` clause we scan).  So recognising these commands is
# faithful, not a `<Prefix>_theorem` name-guess.  Each declared command's
# `kind` maps to one of the existing tag families below; we then route the
# command through the same name/branch logic as the matching built-in.
#
# kind -> family follows Pure/Isar/keyword.scala:
#   theory_goal = {thy_goal, thy_goal_stmt, thy_goal_defn}  (proof-bearing)
#   theory_defn = {thy_defn, thy_goal_defn}                 (introduces a def)
#   thy_decl / thy_decl_block / thy_stmt                    (declarations)
# Proof (prf_*), diagnostic (diag), document, load and quasi_command kinds are
# intentionally absent: they introduce no citable fact, so they must NOT create
# an entry.  `thy_goal_defn` both defines and proves; for a *custom* command of
# that kind we tag it pragmatically as a goal so its name and proof are picked
# up.  (The built-in `function` is the common `thy_goal_defn`, but it is handled
# by DECL_RE as a `FUN` definition — like `fun` — so its constant lands in
# `defs`; the trailing `by`/`termination` proof falls inside the def body span.)
_KIND_FAMILY = {
    "thy_goal": "THEOREM",
    "thy_goal_stmt": "THEOREM",
    "thy_goal_defn": "THEOREM",
    "thy_defn": "DEF",
    "thy_decl": "DEF",
    "thy_decl_block": "DEF",
    "thy_stmt": "DEF",
}

# The union of every scanned header's command table for the active root,
# populated by load_index()'s header pre-scan (mirroring Isabelle's
# session-wide `Keywords.++`).  Empty by default, so a bare extract_entries
# call behaves exactly as before — and every body-scan custom-command check
# is guarded by `if table`, costing nothing when no custom commands exist.
_CUSTOM_COMMANDS: dict[str, str] = {}


def _route_for(keyword: str, tag: str) -> str:
    """Which extract_entries branch handles a command with this tag.

    Derived from the tag (not a second keyword table) so built-in and custom
    commands route uniformly: a custom `thy_goal` command (tag THEOREM) takes
    the same `goal` branch as `theorem`, a custom `thy_decl`/`thy_defn` (tag
    DEF) the same `def` branch as `definition`."""
    if keyword == "axiomatization":
        return "axiom"
    if tag in ("DATATYPE", "TYPE", "RECORD"):
        return "typedecl"
    if tag in ("LEMMA", "THEOREM"):
        return "goal"
    return "def"  # DEF, ABBREV, FUN, INDSET, IND, and custom thy_decl/thy_defn

PROOF_RE = re.compile(
    r"^\s*(proof\b|by\b|sorry\b|oops\b|using\b"
    r"|unfolding\b|apply\b|\.\.\s*$)"
)
BLANK_RE = re.compile(r"^\s*$")
TOPLEVEL_RE = re.compile(r"^[a-z]")

# Outer commands that declare nothing and so are never indexed as entries,
# but which still bound the declaration above them.  `compute_spans` ends an
# entry at the next entry-or-section line; without these an `instance` proof,
# a `lemmas` alias or the `end` of an enclosing block falls INSIDE the
# preceding declaration's span.  Two things then go wrong: the span reported
# by `enclosing` / `outline` / `largest` is inflated, and a fact cited by the
# absorbed command lands in that declaration's own def-site range, where the
# call-graph scan discards it as a self-mention — so the cited fact reads as
# unused.  The canonical case is an `equal` instantiation:
#
#     instantiation foo :: equal begin
#     definition "equal_foo (x::foo) y = (x = y)"
#     instance by standard (simp add: equal_foo_def)
#     end
#
# where `equal_foo` swallows the very `instance` proof that cites it.
_SPAN_BOUNDARY_COMMANDS = frozenset({
    "begin", "end", "instance", "instantiation", "interpretation",
    "sublocale", "locale", "context", "declare", "lemmas", "notation",
    "no_notation", "syntax", "no_syntax", "translations",
    "code_printing", "export_code", "code_datatype", "code_reflect",
    "typedecl", "typedef", "consts", "print_translation",
})
_LEADING_CMD_RE = re.compile(r"^([a-z][a-z_0-9]*)")


def _structural_command_lines(lines: list[str],
                              comment_ranges: "list[range] | None" = None,
                              ) -> list[int]:
    """1-indexed lines that open a span-bounding outer command.

    Fed to :func:`compute_spans` alongside the section lines, so a
    declaration ends where the next outer command begins rather than running
    on through it.  See ``_SPAN_BOUNDARY_COMMANDS``.

    Lines inside ``(* ... *)`` are skipped: a commented-out `end` is prose,
    not a command, and must not cut the declaration above it.
    """
    masked: set[int] = set()
    for r in (comment_ranges or []):
        masked.update(r)
    out: list[int] = []
    for line_no_0, line in enumerate(lines):
        line_no = line_no_0 + 1
        if line_no in masked:
            continue
        m = _LEADING_CMD_RE.match(line)  # column 0: introducer position
        if m is None or m.group(1) not in _SPAN_BOUNDARY_COMMANDS:
            continue
        # Report the boundary at the head of any blank run before the
        # command, so the preceding entry's span ends on its last real line
        # rather than on the separating blank — the same "no trailing
        # blanks" rule the entry-to-entry boundary already follows.
        b = line_no
        while b > 1 and not lines[b - 2].strip():
            b -= 1
        out.append(b)
    return out
SECTION_RE = re.compile(r"^(chapter|section|subsection|subsubsection)\s+\\<open>(.*)")
TEXT_OPEN_RE = re.compile(r"^\s*(text|text_raw)\s*\\<open>")
COMMENT_LINE_RE = re.compile(r"\\<comment>\s*\\<open>(.*)$")
LATEX_LINE_RE = re.compile(
    r"\\(begin|end|caption|node|draw|newlength|newcommand|settowidth|settoheight|scalebox|label)\b"
)
# Isabelle fact/definition names that contain non-identifier characters
# (-, :, [, ], digits after a colon, ...) must be double-quoted at their
# declaration site, e.g. `theorem "beta-C-cor:3":`.  Capture the quoted
# spelling verbatim so `show`/`callers` can find the entry by the name the
# source actually uses.
QUOTED_NAME_RE = re.compile(r'^"([^"]+)"')
# A bare name may interleave ASCII identifier characters with Isabelle
# symbol tokens written `\<...>` (e.g. \<psi>, \<alpha>ah, \<tau>rtrancl3p)
# and subscript controls (\<^sub>1).  Treating `\<...>` runs as name
# characters captures the many AFP entries whose names are Greek letters or
# decorated identifiers, which a plain `\w[\w']*` pattern misses.
SYM_NAME_RE = re.compile(r"((?:\\<\^?\w+>|\w)(?:\\<\^?\w+>|[\w'])*)")
# Isabelle structural control symbols are not fact names: cartouche
# delimiters (\<open>/\<close>) and the comment marker (\<comment>) can sit
# where a name is expected (a cartouche statement, or a `\<comment> \<open>
# ...\<close>` annotation), and must not be captured as the name.
RESERVED_NAME_PREFIXES = ("\\<open>", "\\<close>", "\\<comment>", "\\<^cancel>")
# Outer-syntax keywords that are not fact names.  When the name slot holds one
# of these *bare* — `lemma assumes ...`, `lemma fixes ...`, `... (eqvt) by ...`,
# `lemma shows NAME: ...` — the construct is anonymous (or its true name
# follows), and the keyword must not be captured as the name.  Only the BARE
# form is rejected: a *quoted* keyword (`fun "for"`, `lemma "if":`,
# `definition "and"`) is a legitimate, deliberately-quoted name and is parsed
# by the quoted branch of _name_from before this guard is reached.
_RESERVED_NAME_WORDS = frozenset({
    # Isar statement elements following an (anonymous) lemma/theorem
    "assumes", "shows", "fixes", "obtains", "defines", "notes", "constrains",
    # proof-script keywords
    "by", "using", "unfolding", "apply", "proof", "qed", "done", "oops",
    "sorry",
    # structural keywords that can land in a misparsed name slot
    "where", "for", "and", "if", "then", "else", "next", "case",
})
# A quoted spelling is a *name* only when it forms a label: the closing quote
# is followed, after optional [attributes], by ':'.  Otherwise the quotes hold
# the statement of an anonymous lemma (`lemma "P"`), not a name.
LABEL_AFTER_RE = re.compile(r"\s*(?:\[[^\]]*\]\s*)*:")

# Named conjuncts of a multi-`shows` lemma: `shows NAME:` / `and NAME:`
# in the *shows* region.  Gated by the SHOWS_*_RE so the `assumes ... and
# X:` region — whose `and`-bound names are hypotheses, not citable facts —
# is excluded (shows always follows assumes in Isabelle's lemma grammar).
SHOWS_AT_START_RE = re.compile(r"shows\b")     # applied to a stripped line
SHOWS_ANYWHERE_RE = re.compile(r"\bshows\b")   # applied to the decl-line rest
CONJUNCT_RE = re.compile(r"(?:shows|and)\s+(\w[\w']*)\s*:")


# A fact name that contains a character outside the identifier/symbol set —
# a hyphen, colon, bracket, etc. (`beta-C-cor:3`, `num:1`, `denote=:4[3]`) —
# cannot be written bare in a reference; Isabelle requires it double-quoted.
# Such names are also frequently substrings of one another (`num:1` of
# `eq-num:1`, `safe-ext` of `safe-ext[3]`), so a `[\w']`-boundary search
# spuriously matches the short one inside the long one.
_SPECIAL_NAME_RE = re.compile(r"[^\w'\\<>^]")


def _isa_word_pattern(name: str) -> str:
    r"""Return a regex matching `name` as a complete Isabelle name reference.

    Three cases, each matching exactly where a real citation can occur:

    * **Special-character names** (hyphen/colon/bracket — must be quoted in
      source): match only when flanked by the double-quotes, so `num:1` is
      not found inside `"eq-num:1"`.
    * **Symbolic names** written with `\<...>` tokens: a name that *ends* in
      `>` must not be glued to a following `\<...>` symbol, and one that
      *starts* with `\<` must not follow a preceding `>` — otherwise `\<gamma>`
      would match inside `\<gamma>\<^sub>1`.  (A bare ASCII run abutting a
      symbol, e.g. `foo` in `foo\<gamma>`, is still a match — it does not end
      in `>`.)
    * **Plain identifiers**: a prime-aware word boundary — `\b` is wrong
      because Isabelle allows `'` inside identifiers (`foo'`).
    """
    if _SPECIAL_NAME_RE.search(name):
        return r'(?<=")' + re.escape(name) + r'(?=")'
    left = r"(?<![\w'])" + (r"(?<!>)" if name.startswith("\\<") else "")
    right = (r"(?!\\<)" if name.endswith(">") else "") + r"(?![\w'])"
    return left + re.escape(name) + right


def _balanced_paren_end(s: str) -> int:
    """Index just past the ')' matching a leading '(' (s must start with
    '('), accounting for nesting; -1 if unbalanced."""
    depth = 0
    for i, c in enumerate(s):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i + 1
    return -1


def _balanced_cartouche_end(s: str) -> int:
    r"""Index just past the `\<close>` matching a leading `\<open>` (s must
    start with `\<open>`), accounting for nesting; -1 if unbalanced (e.g. a
    cartouche that runs past the end of this line).  The cartouche is the
    symbol-level analogue of a paren: `\<open>`/`\<close>` nest like `(`/`)`."""
    depth = 0
    i = 0
    while i < len(s):
        if s.startswith("\\<open>", i):
            depth += 1
            i += len("\\<open>")
        elif s.startswith("\\<close>", i):
            depth -= 1
            i += len("\\<close>")
            if depth == 0:
                return i
        else:
            i += 1
    return -1


def _strip_decl_prefix(s: str, typevars: bool) -> str:
    r"""Drop the syntactic noise that can sit between a keyword and the name.

    A fact or type name never starts with '(', a type variable, or a margin
    comment, so this only removes:
      * command modifiers / locale specs — ``(in foo)``, ``(nonexhaustive)``,
        ``(overloaded)``, ``(discs_sels)``, ``(sequential)``, ...
      * a leading margin comment ``\<comment> \<open>...\<close>`` that annotates
        the declaration before its name;
      * for type declarations (``typevars=True``), leading type arguments,
        either bare (``'a``) or grouped (``('a, 'b)``).
    """
    while s:
        if s[0] == "(":
            j = _balanced_paren_end(s)
            if j < 0:
                break
            s = s[j:].lstrip()
            continue
        if s.startswith("\\<comment>"):
            s = s[len("\\<comment>"):].lstrip()
            if s.startswith("\\<open>"):
                k = _balanced_cartouche_end(s)
                if k < 0:
                    break               # comment runs past this line
                s = s[k:].lstrip()
            continue
        if typevars and s[0] == "'":
            m = re.match(r"'[\w']+\s+", s)
            if m:
                s = s[m.end():]
                continue
        break
    return s


def _name_from(s: str, require_label: bool) -> str:
    """Parse a name from `s` (already stripped of any decl prefix): a
    double-quoted spelling, else a symbol-aware identifier, else '?'.

    With ``require_label`` (fact commands), a quoted spelling counts only as a
    *label* — followed, after optional [attributes], by ':'.  Otherwise the
    quotes hold the statement of an anonymous lemma (`lemma "P"`), not a name.
    Type declarations pass ``require_label=False``: a quoted type name
    (`datatype 'a "term"`) is followed by '=' / where, not ':'.
    """
    mq = QUOTED_NAME_RE.match(s)
    if mq and (not require_label or LABEL_AFTER_RE.match(s, mq.end())):
        return mq.group(1)
    m = SYM_NAME_RE.match(s)
    if not m:
        return "?"
    name = m.group(1)
    if name.startswith(RESERVED_NAME_PREFIXES) or name in _RESERVED_NAME_WORDS:
        return "?"
    return name


def _parse_name(text_after_tag: str) -> str:
    return _name_from(_strip_decl_prefix(text_after_tag.strip(), typevars=False),
                      require_label=True)


def _parse_typedecl_name(text_after_tag: str) -> str:
    r"""Parse a type_synonym / datatype / record's name, skipping any
    leading modifier (\<open>(discs_sels)\<close>) and type-argument list
    (\<open>'a\<close> or \<open>('a, 'b)\<close>)."""
    return _name_from(_strip_decl_prefix(text_after_tag.strip(), typevars=True),
                      require_label=False)


# A definitional connective: an implicit-name definition/abbreviation is
# written as a quoted equation `"lhs ... <connective> rhs"`.  Its presence is
# the signal that the quoted body is an equation whose LHS head is the name.
_DEF_CONNECTIVE_RE = re.compile(r"\\<equiv>|\\<rightleftharpoons>|==|=")


def _lhs_head_name(text_after_tag: str) -> str:
    r"""Head name of an implicit-name definition/abbreviation written as a
    quoted equation: `abbreviation "language_ltlc \<phi> \<equiv> ..."` ->
    ``language_ltlc``.  The name is the first identifier of the LHS — the
    constant being defined.

    Returns '?' unless the leading token (after any modifier/locale prefix) is
    a quoted body that actually contains a definitional connective, so a quoted
    *statement* (an anonymous `lemma "P"`) is never mistaken for a definition.
    Only the prefix-application case is handled; infix/mixfix definitions,
    whose operator sits between operands, are out of scope and stay '?'."""
    s = _strip_decl_prefix(text_after_tag.strip(), typevars=False)
    mq = QUOTED_NAME_RE.match(s)
    if not mq or not _DEF_CONNECTIVE_RE.search(mq.group(1)):
        return "?"
    return _name_from(mq.group(1).strip(), require_label=False)


def _parse_def_name(text_after_tag: str) -> str:
    """Name of a definition/abbreviation: a leading label/identifier as usual,
    else the LHS head of an implicit-name quoted equation."""
    name = _parse_name(text_after_tag)
    return name if name != "?" else _lhs_head_name(text_after_tag)


# The column-0 leading token of a line — the candidate command name for a
# custom-command match.  Anchored like DECL_RE: an indented line (proof body)
# has no match, so only top-level commands are considered.
_LEAD_TOKEN_RE = re.compile(r"^(\S+)")
# The header `keywords ... ` clause and its terminators (`abbrevs` / `begin`).
# Isabelle's header grammar (thy_header.ML:168) is
#   theory NAME imports ... [keywords <decls>] [abbrevs ...] begin
# so the keyword block runs from the `keywords` token to `abbrevs`/`begin`.
_HEADER_KEYWORDS_RE = re.compile(r"^\s*keywords\b")
_HEADER_BEGIN_RE = re.compile(r"^\s*begin\b")
_HEADER_END_RE = re.compile(r"^\s*(?:abbrevs|begin)\b")
# Tokeniser for the keyword block: a double-quoted name, else a bare run.
_KW_TOK_RE = re.compile(r'"([^"]*)"|(\S+)')


def _kw_tokenize(block: str) -> list[tuple[str, str]]:
    """Split a keyword block into ('name', value) for each double-quoted
    spelling and ('op', text) for every other run.  Quoting matters: a
    command name is always quoted, while the kind, load command and `% tags`
    are bare or quoted-but-after-`::`, so quoting lets us take names only from
    before the `::` and never mistake a `% "proof"` tag value for a name."""
    toks: list[tuple[str, str]] = []
    for m in _KW_TOK_RE.finditer(block):
        if m.group(1) is not None:
            toks.append(("name", m.group(1)))
        else:
            toks.append(("op", m.group(2)))
    return toks


def _kind_of(tok: str) -> str:
    """The leading identifier of a kind token (`thy_goal` from `thy_goal`,
    or from a glued `::thy_goal`'s tail)."""
    m = re.match(r"[A-Za-z_]+", tok)
    return m.group(0) if m else ""


def _parse_keyword_block(block: str, table: dict[str, str]) -> None:
    r"""Parse a header keyword block into ``table`` {command_name: tag}.

    Grammar (Pure/Thy/thy_header.ML:154-164):
      keyword_decls = and_list1(keyword_decl)
      keyword_decl  = repeat1(quoted_name) , optional( "::" kind (load)? (% tag)* )
    The names in one `and`-group share the single optional kind that follows
    them; a group with no `::` is a *minor* keyword (syntax), not a command, so
    it introduces no entry.  Only kinds in :data:`_KIND_FAMILY` map to a tag.
    """
    # Split the token stream into `and`-separated groups (the decl separator).
    groups: list[list[tuple[str, str]]] = [[]]
    for flag, val in _kw_tokenize(block):
        if flag == "op" and val == "and":
            groups.append([])
        else:
            groups[-1].append((flag, val))
    for g in groups:
        names: list[str] = []
        kind = ""
        seen_colon = False
        for flag, val in g:
            if not seen_colon and flag == "op" and val.startswith("::"):
                seen_colon = True
                if val != "::":            # glued `::thy_goal`
                    kind = _kind_of(val[2:])
                continue
            if seen_colon:
                if not kind and flag == "op":   # the kind, just after `::`
                    kind = _kind_of(val)
                continue                        # ignore load command / % tags
            if flag == "name":
                names.append(val)
        tag = _KIND_FAMILY.get(kind)
        if tag:
            for nm in names:
                if nm:
                    table[nm] = tag


def scan_keywords(lines: list[str]) -> dict[str, str]:
    """Return {command_name: tag} for the custom commands a theory's *own*
    header declares.  Scans only the header (up to the theory's `begin`), so
    it is cheap and never touches the body."""
    table: dict[str, str] = {}
    start = None
    for idx, line in enumerate(lines):
        if _HEADER_KEYWORDS_RE.match(line):
            start = idx
            break
        if _HEADER_BEGIN_RE.match(line):
            return table  # header ended (no keywords clause)
    if start is None:
        return table
    block = [re.sub(r"^\s*keywords\b", "", lines[start], count=1)]
    for line in lines[start + 1:]:
        if _HEADER_END_RE.match(line):
            break
        block.append(line)
    _parse_keyword_block(" ".join(block), table)
    return table


def _match_decl(line: str, table: dict[str, str]
                ) -> tuple[str, str, str] | None:
    """Return (keyword, tag, route) if `line` begins a recognised top-level
    command, else None.  Built-in commands match :data:`DECL_RE`; a custom
    command matches when the column-0 leading token is a name in ``table``
    (the scanned keyword table).  When ``table`` is empty this collapses to a
    single DECL_RE test — the pre-scan-free fast path used by every unit test
    and by non-custom theories."""
    m = DECL_RE.match(line)
    if m:
        kw = m.group(1)
        tag = TAG_MAP[kw]
        return kw, tag, _route_for(kw, tag)
    if table:
        m2 = _LEAD_TOKEN_RE.match(line)
        if m2:
            tag = table.get(m2.group(1))
            if tag:
                kw = m2.group(1)
                return kw, tag, _route_for(kw, tag)
    return None


# A decl keyword may stand alone on its line with the name on a *following*
# line (~1,866 AFP entries):
#     inductive_set
#       myset :: "nat set"
#     definition
#       foo :: "nat" where "foo = 0"
# Bound the forward scan to a few lines so a truncated/malformed file cannot
# run on looking for a name that is not there.
_NAME_LOOKAHEAD_LINES = 3


def _lookahead_name(lines: list[str], start: int, table: dict[str, str],
                    parse_fn) -> str:
    r"""The name for a decl whose keyword stood alone: scan forward from the
    0-indexed line ``start``, skipping blank / ``\<comment>`` / ``text`` lines,
    and parse the name from the **first content line** with ``parse_fn``.

    Only the first content line is consulted: a continuation name always sits
    immediately after the keyword.  If that line is an anonymous quoted
    statement (``definition "lhs = ..."``) ``parse_fn`` rightly yields ``'?'``
    — the decl really is anonymous, and scanning on would invent a name from
    unrelated following prose.  A following *top-level command* likewise means
    no name here.  Does NOT consume lines — the caller's body scan still covers
    the peeked line, so the body buffer, ``decl_end_line`` and spans are
    exactly as before; only the name changes."""
    end = min(len(lines), start + _NAME_LOOKAHEAD_LINES)
    j = start
    while j < end:
        stripped = lines[j].strip()
        if not stripped or stripped.startswith("\\<comment>") \
                or TEXT_OPEN_RE.match(lines[j]):
            j += 1
            continue
        if _match_decl(lines[j], table):     # next command — no name here
            return "?"
        return parse_fn(stripped)            # first content line is the name
    return "?"


def extract_sections(lines: list[str]) -> list[tuple[str, str, int]]:
    out: list[tuple[str, str, int]] = []
    for i, line in enumerate(lines, 1):
        m = SECTION_RE.match(line)
        if not m:
            continue
        level = m.group(1)
        rest = m.group(2)
        close_idx = rest.find("\\<close>")
        title = rest[:close_idx] if close_idx >= 0 else rest
        out.append((level, title.strip(), i))
    return out


def _find_balanced_close(lines: list[str], start: int) -> int:
    """Given a 0-indexed start line that opens a `\\<open>` block, return the
    0-indexed line of the matching `\\<close>` (counts open/close balance).
    Returns start if no balance found (malformed).
    """
    depth = 0
    for i in range(start, len(lines)):
        depth += lines[i].count("\\<open>")
        depth -= lines[i].count("\\<close>")
        if depth <= 0 and i >= start:
            return i
    return start


def _line_mask(n: int, spans: Iterable[tuple[int, int]]) -> bytearray:
    r"""A 1-indexed byte mask over ``n`` lines: ``mask[i]`` is 1 iff line ``i``
    lies in some inclusive ``[lo, hi]`` span.  Length ``n + 2`` so a probe at
    line ``n`` (or a ``+1`` sentinel) stays in bounds; each span is clamped to
    ``[1, n]`` and marked C-side by slice assignment.  Shared by the parse-time
    ``text``-block skip and the per-line prose / noise masks of the call-graph
    and method scans.
    """
    mask = bytearray(n + 2)
    for lo, hi in spans:
        lo = max(1, lo)
        hi = min(hi, n)
        if lo <= hi:
            mask[lo:hi + 1] = b"\x01" * (hi - lo + 1)
    return mask


def _scan_balanced_blocks(lines: list[str],
                          opens: Callable[[str], bool]
                          ) -> list[tuple[int, int]]:
    r"""Return [(start, end)] (1-indexed inclusive) for each balanced
    ``\<open>...\<close>`` block whose first line satisfies ``opens``, skipping
    past each block found.  Shared by `extract_text_blocks` (text / text_raw
    cartouches) and `extract_comment_ranges` (``\<comment>`` bodies), which
    differ only in that opening-line predicate.
    """
    out: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        if opens(lines[i]):
            end = _find_balanced_close(lines, i)
            out.append((i + 1, end + 1))
            i = end + 1
        else:
            i += 1
    return out


def extract_text_blocks(lines: list[str]) -> list[tuple[int, int]]:
    """Return [(start_line, end_line)] (1-indexed inclusive) for top-level
    `text \\<open>...\\<close>` and `text_raw` blocks.  Body is not stored —
    callers slice from sec.source() when needed.
    """
    return _scan_balanced_blocks(lines, lambda ln: bool(TEXT_OPEN_RE.match(ln)))


def extract_comment_ranges(lines: list[str]) -> list[tuple[int, int]]:
    """Return [(start_line, end_line)] (1-indexed inclusive) for every
    \\<comment> \\<open>...\\<close> annotation, including multi-line bodies.

    Tracks \\<open>/\\<close> balance starting from the line that contains
    \\<comment>.  A \\<comment> on a line without \\<open> yields a single-
    line range (covers tag-only annotations without explicit body).
    """
    return _scan_balanced_blocks(lines, lambda ln: "\\<comment>" in ln)


def extract_comment_lines(lines: list[str]) -> list[tuple[int, str]]:
    """Return [(line_no, content)] for in-proof `\\<comment> \\<open>...\\<close>`
    annotations.  `content` is the prose text inside the `\\<open>...\\<close>`
    on the comment's first line (truncated at the first `\\<close>` if present).
    """
    out = []
    for i, line in enumerate(lines, 1):
        m = COMMENT_LINE_RE.search(line)
        if not m:
            continue
        rest = m.group(1)
        close_idx = rest.find("\\<close>")
        content = rest[:close_idx] if close_idx >= 0 else rest
        out.append((i, content.strip()))
    return out


def extract_entries(lines: list[str],
                    custom: dict[str, str] | None = None) -> list[Entry]:
    entries: list[Entry] = []
    i = 0

    # Recognised custom commands: this theory's own header declarations, the
    # active root's scanned union (_CUSTOM_COMMANDS, set by load_index), and an
    # explicit `custom` override (tests).  Empty for a plain theory with no
    # `keywords` clause, in which case _match_decl is just a DECL_RE test.
    table: dict[str, str] = dict(_CUSTOM_COMMANDS)
    table.update(scan_keywords(lines))
    if custom:
        table.update(custom)

    # Prose inside a `text \<open>...\<close>` / `text_raw` cartouche is a single
    # token to Isabelle, never outer syntax.  A column-0 line *inside* such a
    # block that happens to begin with a command name — notably a one-letter
    # command such as Isabelle_C's `C` — is prose, not a declaration, so we
    # skip those lines and never mint a phantom entry (or phantom span
    # boundary) from them.  (1-indexed; in_text[i+1] guards source line i+1.)
    in_text = _line_mask(len(lines), extract_text_blocks(lines))

    while i < len(lines):
        line = lines[i]
        if in_text[i + 1]:
            i += 1
            continue
        md = _match_decl(line, table)
        if md is None:
            i += 1
            continue

        keyword, tag, route = md
        decl_line = i + 1  # 1-indexed source line

        # --- Simple one-concept declarations ---
        if route == "typedecl":
            rest = line[len(keyword):].strip()
            rest = re.sub(r"\s+where$", "", rest)
            name = _parse_typedecl_name(rest)
            if name == "?" and not _strip_decl_prefix(rest, typevars=True):
                name = _lookahead_name(lines, i + 1, table,
                                       _parse_typedecl_name)
            e = Entry(tag, name, f"{tag} {rest}",
                      thy_line=decl_line, decl_end_line=decl_line)
            entries.append(e)
            i += 1
            continue

        if route == "axiom":
            entries.append(Entry("AXIOM", "axiomatization", "AXIOMATIZATION",
                                 thy_line=decl_line, decl_end_line=decl_line))
            i += 1
            while i < len(lines):
                ax_line = lines[i].strip()
                if re.match(r"[a-z_]+\s*:", ax_line):
                    name = ax_line.split(":")[0].strip()
                    ax_entry = Entry("AXIOM", name, f"  AXIOM {ax_line}",
                                     thy_line=i + 1, decl_end_line=i + 1)
                    entries.append(ax_entry)
                    i += 1
                elif ax_line.startswith("and "):
                    i += 1
                elif ax_line == "" or TOPLEVEL_RE.match(lines[i]):
                    break
                else:
                    i += 1
            continue

        # --- Definitions ---
        if route == "def":
            rest = line[len(keyword):].strip()
            rest = re.sub(r"\s+where$", "", rest)
            # definition/abbreviation may carry an implicit name in a quoted
            # equation (`"lhs \<equiv> ..."`); read its LHS head when no label.
            parse_fn = (_parse_def_name
                        if keyword in ("definition", "abbreviation")
                        else _parse_name)
            name = parse_fn(rest)
            if name == "?" and not _strip_decl_prefix(rest, typevars=False):
                name = _lookahead_name(lines, i + 1, table, parse_fn)
            buf = [f"{tag} {rest}"]
            decl_end_line = decl_line
            i += 1
            open_quotes = rest.count('"') % 2
            past_where = False  # for `definition`/`abbreviation`: tracks whether
                                # the body's quoted RHS has begun, so we don't
                                # break at the type signature's closing quote.
            while i < len(lines):
                cline = lines[i]
                if BLANK_RE.match(cline):
                    break
                if _match_decl(cline, table):
                    break
                stripped = cline.strip()
                if stripped.startswith("\\<comment>") or stripped.startswith("text "):
                    break
                where_on_this_line = bool(re.search(r"\bwhere\b", stripped))
                buf.append(f"  {stripped}")
                open_quotes = (open_quotes + stripped.count('"')) % 2
                i += 1
                decl_end_line = i  # 1-indexed line just appended
                if keyword in ("definition", "abbreviation"):
                    # Break when the body's quoted RHS closes (after `where`).
                    if past_where and open_quotes == 0 and '"' in stripped:
                        break
                    if where_on_this_line:
                        past_where = True
            entries.append(Entry(tag, name, "\n".join(buf),
                                 thy_line=decl_line,
                                 decl_end_line=decl_end_line))
            continue

        # --- Lemmas / theorems / corollaries ---
        if route == "goal":
            rest = line[len(keyword):].strip()
            name = _parse_name(rest)
            buf = [f"{tag} {rest}"]
            decl_end_line = decl_line
            proof_line = 0
            # Named conjuncts: scan the `shows` region only.  `shows` may
            # appear inline on the decl line (one-liner) or on its own line.
            in_shows = bool(SHOWS_ANYWHERE_RE.search(rest))
            conjuncts: list[str] = (
                CONJUNCT_RE.findall(rest) if in_shows else [])
            i += 1

            while i < len(lines):
                cline = lines[i]
                stripped = cline.strip()
                if BLANK_RE.match(cline):
                    break
                if PROOF_RE.match(cline):
                    proof_line = i + 1
                    break
                if _match_decl(cline, table):
                    break
                if stripped.startswith("\\<comment>"):
                    i += 1
                    continue
                if SHOWS_AT_START_RE.match(stripped):
                    in_shows = True
                if in_shows:
                    conjuncts.extend(CONJUNCT_RE.findall(stripped))
                buf.append(f"  {stripped}")
                i += 1
                decl_end_line = i

            entries.append(Entry(tag, name, "\n".join(buf),
                                 thy_line=decl_line,
                                 decl_end_line=decl_end_line,
                                 proof_line=proof_line,
                                 conjuncts=conjuncts))
            continue

        i += 1

    return entries


def compute_spans(entries: list[Entry], section_lines: list[int],
                  total_lines: int) -> None:
    """Set thy_end on each entry to the line before the next entry-or-section.

    The boundary above an entry is the *next entry's* ``src_start`` — its
    leading `text` preamble if it has one, else its declaration line — so a
    following entry's docstring is charged to *that* entry, not folded into
    the preceding entry's span (the `[src-doc-attribution]` fix).  Run after
    ``_attach_preambles`` so ``src_start`` is known.

    ``structural`` is sorted, so the next boundary above an entry is a
    ``bisect`` away — the old ``[s for s in structural if s > e.thy_line]``
    rescanned the whole list per entry, making this O(entries^2).  That is
    invisible on a typical theory but the dominant parse cost on an
    entry-dense one (e.g. a file of thousands of short declarations).
    """
    structural = sorted({e.src_start for e in entries if e.thy_line > 0}
                        | set(section_lines))
    n = len(structural)
    for e in entries:
        # Bisect on the *declaration* line (not src_start): the boundary must
        # lie strictly after this entry's own decl, so an entry's own preamble
        # start never reads as its end.
        idx = bisect_right(structural, e.thy_line)
        e.thy_end = (structural[idx] - 1) if idx < n else total_lines


def _attach_preambles(entries: list[Entry], lines: list[str],
                      text_blocks: list[tuple[int, int]]) -> None:
    """Attach each leading `text` block to the entry it documents (preamble).

    Preamble: text block whose `end` line is within ~3 blank lines of an
    entry's `thy_line`.  Avoids attaching a giant top-of-file narrative
    to the very first entry hundreds of lines later.

    Runs *before* ``compute_spans`` — the preamble fixes the entry's
    ``src_start``, which `compute_spans` then uses as the boundary so the doc
    is charged to this entry, not the preceding one.
    """
    # --- preambles: text block → next entry, only if adjacent AND small ---
    # Both conditions matter: a 500-line section narrative just before the
    # first definition is NOT that definition's docstring; it's the chapter's
    # introduction.  See UTM.thy lines 28-530 for the canonical example.
    #
    # entry_starts is sorted, so the entry just below a block is a bisect away —
    # the old per-block linear scan over all entries was O(text_blocks x
    # entries), quadratic on a theory dense in both.
    PREAMBLE_MAX_LINES = 30
    entry_starts = sorted([(e.thy_line, e) for e in entries if e.thy_line > 0])
    starts_keys = [es for es, _ in entry_starts]
    n = len(entry_starts)
    for tb_start, tb_end in text_blocks:
        if tb_end - tb_start + 1 > PREAMBLE_MAX_LINES:
            continue  # too big to be a per-entry docstring
        idx = bisect_right(starts_keys, tb_end)  # first entry starting past tb_end
        if idx >= n:
            continue
        es, e = entry_starts[idx]
        # Are intervening lines (tb_end+1 .. es-1) all blank?
        gap = lines[tb_end:es - 1]
        if all(not l.strip() for l in gap) and len(gap) <= 3:
            e.preamble = (tb_start, tb_end)


def _attach_roadmaps(entries: list[Entry],
                     comment_lines: list[tuple[int, str]]) -> None:
    """Attach each in-proof \\<comment> line (roadmap) to its owning entry.

    Roadmap: \\<comment> line whose line number lies inside the entry's
    proof span [proof_line+1 .. thy_end].  Runs *after* ``compute_spans`` —
    it reads ``thy_end`` to bound the proof body.
    """
    # Spans are non-overlapping, so the only candidate is the entry whose
    # thy_line is the greatest <= cline; attach iff cline is in its proof body.
    # entry_starts is sorted, so the enclosing entry is a bisect away (the old
    # per-comment scan over all entries was O(comments x entries)).
    entry_starts = sorted([(e.thy_line, e) for e in entries if e.thy_line > 0])
    starts_keys = [es for es, _ in entry_starts]
    for cline, content in comment_lines:
        idx = bisect_right(starts_keys, cline) - 1
        if idx < 0:
            continue
        e = entry_starts[idx][1]
        if e.proof_line and e.proof_line < cline <= e.thy_end:
            e.roadmap.append((cline, content))


def _parse_one(thy: str, thy_path: Path,
               lines: list[str] | None = None) -> TheorySection:
    """Parse a theory's source into a fully-populated TheorySection.

    `lines`, when supplied, is already-read source parsed *in place of*
    reading `thy_path` from disk — the path taken by the `-` stdin sentinel,
    whose `thy_path` is synthetic (`<stdin>`) and has nothing to read.  In
    that case the section caches the lines so a later `source()` call never
    falls back to reading the non-existent path.
    """
    from_memory = lines is not None
    if lines is None:
        lines = thy_path.read_text().splitlines()
    entries = extract_entries(lines)
    outline = extract_sections(lines)
    text_blocks = extract_text_blocks(lines)
    comment_ranges = extract_comment_ranges(lines)
    comment_lines = extract_comment_lines(lines)
    # Preambles first: they fix each entry's src_start, which compute_spans
    # uses as the boundary so a leading doc is charged to the entry it
    # documents (not the preceding one).  Roadmaps need the resulting thy_end.
    _attach_preambles(entries, lines, text_blocks)
    compute_spans(entries,
                  [s[2] for s in outline]
                  + _structural_command_lines(lines, comment_ranges),
                  len(lines))
    _attach_roadmaps(entries, comment_lines)
    for e in entries:
        e.theory = thy
    # Compute body_end_line: for entries with a proof, walk forward from
    # proof_line through proof / by / qed / blank lines, stopping at the
    # next text \<open>...\<close> block or declaration.  For pure
    # declarations (no proof), body ends at decl_end_line.  Computed after
    # compute_spans because _proof_extent needs thy_end as a search bound.
    sec_for_extent = TheorySection(thy, thy_path, entries, thy_lines=len(lines))
    sec_for_extent._source_cache = lines
    for e in entries:
        if e.proof_line:
            e.body_end_line = _proof_extent(sec_for_extent, e.proof_line, e.thy_end)
        else:
            e.body_end_line = e.decl_end_line or e.thy_line
    sec = TheorySection(thy, thy_path, entries, thy_lines=len(lines),
                        outline=outline, text_blocks=text_blocks,
                        comment_ranges=comment_ranges)
    if from_memory:
        # No disk path to lazily re-read (stdin); pin the source we already have.
        sec._source_cache = lines
    return sec


def _parse_plain(thy: str, path: Path,
                 lines: list[str] | None = None) -> TheorySection:
    """Build a *plain* section for a non-`.thy` file (e.g. a design memo
    passed as a grep positional).  The Isabelle entry/section/comment
    grammar does not apply to Markdown or prose, so we deliberately skip
    `extract_entries` and friends: a plain section has no entries, no
    outline, and no text/comment ranges.  cmd_grep then degrades to
    ordinary line-based `grep` over it — no synthesised owning-entry
    labels, no live/comment classification (every match is reported).

    `lines`, when supplied, is already-read source (the stdin path), parsed
    in place of reading `path` — symmetric with `_parse_one`."""
    if lines is None:
        lines = path.read_text().splitlines()
    sec = TheorySection(thy, path, [], thy_lines=len(lines), is_thy=False)
    sec._source_cache = lines
    return sec


def _add_one_section(thy: str, thy_path: Path,
                     seen_paths: set[Path],
                     sections: list[TheorySection]) -> None:
    """Append a parsed section, deduplicating by resolved absolute path
    so that symlinked theories (e.g.\\ `link/Foo.thy`
    -> `sub/Foo.thy`) appear once even if both the symlink
    and the target are encountered.

    `.thy` paths are parsed with the full Isabelle entry grammar
    (`_parse_one`); any other path is parsed plainly (`_parse_plain`)
    so grep over a Markdown/prose file does not invent bogus entries."""
    if not thy_path.exists():
        return
    resolved = thy_path.resolve()
    if resolved in seen_paths:
        return
    seen_paths.add(resolved)
    if thy_path.suffix == ".thy":
        sections.append(_parse_one(thy, thy_path))
    else:
        sections.append(_parse_plain(thy, thy_path))


def _scan_header_file(path: Path) -> dict[str, str]:
    r"""Scan only a theory's *header* for its `keywords` clause.

    Reads at most a few hundred lines (a header is short — `theory ... begin`),
    stopping at the theory's `begin`, so this is cheap even at AFP scale and
    never touches proof bodies."""
    head: list[str] = []
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            for n, line in enumerate(f):
                head.append(line.rstrip("\n"))
                if n >= 400 or _HEADER_BEGIN_RE.match(line):
                    break
    except OSError:
        return {}
    return scan_keywords(head)


def _populate_custom_commands(pairs: list[tuple[str, Path]]) -> None:
    """Merge every theory header's custom-command table into the active
    root's union :data:`_CUSTOM_COMMANDS` — mirroring Isabelle's session-wide
    ``Keywords.++`` (Pure/Isar/keyword.scala:151).  This is what lets a theory
    that *uses* `AOT_theorem` be parsed correctly even though the command is
    *declared* in a different theory's header.  (Cleared by load_index before
    the scan; a name redeclared with a different kind takes the last seen.)"""
    for _name, path in pairs:
        if path.suffix == ".thy" and path.exists():
            _CUSTOM_COMMANDS.update(_scan_header_file(path))


def _sections_from_dir(root_dir: Path,
                       seen_paths: set[Path],
                       sections: list[TheorySection]) -> None:
    """Enumerate theories under `root_dir` and append parsed sections.

    Walks every ROOT file under `root_dir` (via `discover_roots`) and
    each session declared in each ROOT (via `parse_root_sessions`).
    Theories are resolved against the declaring session's directory,
    honouring its `in <subdir>` and `directories` clauses (so a theory
    a session declares to live `in "sub"` is found under `sub/`, not
    beside its ROOT file).

    Falls back to a recursive `*.thy` glob if no ROOTs are found
    (legacy behaviour for non-Isabelle-session directories).  Dedup
    by resolved path via `_add_one_section`.

    Two phases: first collect the theory list, then pre-scan all headers to
    build the custom-command union (so a use can precede its declaration in
    parse order), then parse each theory's entries.
    """
    roots = discover_roots(root_dir)
    pairs: list[tuple[str, Path]] = []
    if roots:
        for root_path in roots:
            for session in parse_root_sessions(root_path):
                for thy_entry in session.theories:
                    thy_path = resolve_session_theory(session, thy_entry)
                    if thy_path is None:
                        continue
                    pairs.append((thy_entry[0], thy_path))
    else:
        for thy_path in sorted(root_dir.rglob("*.thy")):
            pairs.append((thy_path.stem, thy_path))

    _populate_custom_commands(pairs)
    for name, thy_path in pairs:
        _add_one_section(name, thy_path, seen_paths, sections)


_ROOT_OVERRIDE: Path | None = None  # set by main() from --root


def active_t_dir() -> Path:
    """The session directory the index is built from: the `--root`
    override if `main()` set one, else :func:`default_t_dir` (which
    consults `$ISABELLE_QUERY_ROOT` and walks up from the cwd)."""
    return _ROOT_OVERRIDE if _ROOT_OVERRIDE is not None else default_t_dir()


def load_index() -> list[TheorySection]:
    """Walk the active session directory, parsing each declared theory.
    Searches at the session root and in any sub-directory declared by
    ROOT's `directories` clause.  See :func:`active_t_dir` for how the
    directory is resolved (`--root` / `$ISABELLE_QUERY_ROOT` / cwd discovery)."""
    sections: list[TheorySection] = []
    seen_paths: set[Path] = set()
    _CUSTOM_COMMANDS.clear()  # rebuilt per load from the active root's headers
    _sections_from_dir(active_t_dir(), seen_paths, sections)
    return sections


# ---------------------------------------------------------------------------
# Call graph and shared filter helpers — `_noise_ranges` /
# `_build_def_sites` underpin both single-name search (`_find_callers`)
# and bulk graph construction (`_build_call_graph`).  `_bfs_depths` is the
# single BFS behind every -r form (callers/callees, deps/uses).
# ---------------------------------------------------------------------------

def _build_line_index(sections: list[TheorySection]
                      ) -> dict[str, list[tuple[int, int, Entry]]]:
    """For each theory, build a sorted list of (src_start, thy_end, Entry)
    for binary-search lookup of which entry owns a given line.  The span
    starts at ``src_start`` (the leading preamble, if any) so a doc line
    resolves to the entry it documents, not the preceding one."""
    index: dict[str, list[tuple[int, int, Entry]]] = {}
    for sec in sections:
        spans = [(e.src_start, e.thy_end, e) for e in sec.entries
                 if e.thy_line > 0]
        spans.sort()
        index[sec.theory] = spans
    return index


_FIRST = itemgetter(0)  # span start, for keyed bisect into a line index


def _entry_at_line(line_index: list[tuple[int, int, Entry]],
                   line_no: int) -> Entry | None:
    """Binary search for the entry whose [src_start, thy_end] contains line_no.

    `bisect` reads each probed span's start via `key=` (a C-level itemgetter),
    so the search touches O(log n) elements — the old form rebuilt a full
    `[s[0] for s in line_index]` keys list on *every* call, which at corpus
    scale (one call per source line) dominated the build profile.
    """
    idx = bisect_right(line_index, line_no, key=_FIRST) - 1
    if idx < 0:
        return None
    start, end, entry = line_index[idx]
    if start <= line_no <= end:
        return entry
    return None


def _sections_by_theory(sections: list[TheorySection]
                        ) -> dict[str, TheorySection]:
    """Index sections by theory name (theory → section)."""
    return {s.theory: s for s in sections}


def _entry_by_name(sections: list[TheorySection]
                   ) -> dict[str, tuple[str, Entry]]:
    """First-wins index of entry name → (theory, Entry).

    First-wins: when a name is defined in more than one theory the earliest
    section in load order owns the lookup — matching every call site that
    previously built this map inline.
    """
    by_name: dict[str, tuple[str, Entry]] = {}
    for sec in sections:
        for e in sec.entries:
            if e.name not in by_name:
                by_name[e.name] = (sec.theory, e)
    return by_name


def _noise_spans(sec: TheorySection) -> list[tuple[int, int]]:
    r"""Inclusive ``[lo, hi]`` line spans of `sec` that are NOT live source:
    top-level ``text``/``text_raw`` blocks, multi-line ``\<comment>``
    annotations, and per-entry preambles.  The single definition of "prose,
    not proof" — `grep`, `methods`, the call graph (via `_noise_ranges`), and
    the proof-block drill-down all skip exactly these lines, so the notion can
    no longer drift between them.
    """
    return (list(sec.text_blocks) + list(sec.comment_ranges)
            + [e.preamble for e in sec.entries if e.preamble])


def _noise_ranges(sections: list[TheorySection]) -> dict[str, list[range]]:
    r"""Per-theory ``range`` objects for the non-live (prose) line spans —
    each section's :func:`_noise_spans` as ``range``s for membership tests.
    Used by single-name search (`_find_callers`) and bulk graph construction
    (`_build_call_graph`) — the oracle shares it — so both treat
    ``text``/``\<comment>``/preamble mentions as documentation, not calls.
    """
    return {sec.theory: [range(lo, hi + 1) for lo, hi in _noise_spans(sec)]
            for sec in sections}


def _build_def_sites(sections: list[TheorySection],
                     names: set[str] | None = None,
                     ) -> dict[str, dict[str, set[range]]]:
    """Per-theory map of definition-site line ranges, keyed by entry name.

    Used to exclude the definition itself from a search for references
    to that name.  When ``names`` is given, only those names are tracked;
    otherwise every entry with a source location is included.

    Result shape: ``def_sites[theory][name] = {range(thy_line, thy_end+1), ...}``
    """
    def_sites: dict[str, dict[str, set[range]]] = {}
    for sec in sections:
        site_map: dict[str, set[range]] = {}
        for e in sec.entries:
            if e.thy_line <= 0:
                continue
            if names is None or e.name in names:
                site_map.setdefault(e.name, set()).add(
                    range(e.thy_line, e.thy_end + 1))
            # A named conjunct's declaration site is its parent's span, so a
            # `callers CONJUNCT` search excludes the `shows ... and C:` line.
            # Restricted to explicitly-queried names (never the names=None
            # broad pass) so conjuncts don't leak into the call-graph universe.
            if names is not None:
                for c in e.conjuncts:
                    if c in names:
                        site_map.setdefault(c, set()).add(
                            range(e.thy_line, e.thy_end + 1))
        def_sites[sec.theory] = site_map
    return def_sites


# Method-argument modifiers parsed inline by individual methods, so they have
# no declaration site of their own (and are absent from _isabelle_namespace);
# a short, auditable tier-2 list to go with the source-derived namespaces.
_ARG_MODIFIERS = frozenset({"add", "del", "only", "OF", "THEN"})
# Tokens that are never a *fact citation*: proof methods (`by simp`),
# attributes (`[OF g]`), keywords (`proof`, `and`), inline argument modifiers,
# and bare numerals.  A call-graph edge is created only for a name that passes
# _is_citation_name, so an entry that merely happens to be *named* after one of
# these — Isabelle_Meta_Model's `definition "simp"`, a `definition "1 = ..."`,
# an ML `fun lemma` misread as a command — does not collect a spurious in-edge
# from every `by simp` / numeral in the corpus.  The entry still exists for
# show/largest/defs; it is simply not a node in the *citation* graph.  Method
# occurrences are recovered separately by the `methods` query, so this routes
# rather than discards.
_NON_CITATION = (_isa_ns.PROOF_METHODS | _isa_ns.ATTRIBUTES
                 | _isa_ns.KEYWORDS | _ARG_MODIFIERS)


_DROP_NAMES_UPTO = 1   # default; overridden per-invocation via --drop-names-upto


def _is_citation_name(name: str, drop_upto: int = _DROP_NAMES_UPTO) -> bool:
    """Whether a name can denote a cited fact, vs a method/attribute/keyword/
    numeral token *or a name too short to tell apart from a term variable*.
    Shared by the fast builder and the brute-force oracle so both implement
    the same citation semantics.

    ``drop_upto`` filters out citation names of length <= it.  A length-1
    token (`x`, `a`, `f`, the wildcard `_`) is a bound variable in nearly
    every proof, so by default (``drop_upto`` = 1) length-1 names are not
    citation nodes — on the AFP they carry ~28% of all in-edges across 51
    universal-variable names, essentially all noise.  Length-2+ is kept,
    preserving genuine short lemma names (`le`, `id`, `or`).  ``drop_upto`` = 0
    disables the length filter (keep single-char names); 2 also drops 2-char
    names (more aggressive).  See ``scripts/analyze_citation_names.py`` for
    the AFP evidence; the ``--drop-names-upto N`` flag sets it.  The
    method/keyword/numeral router is independent of ``drop_upto``.
    """
    return (len(name) > drop_upto
            and name not in _NON_CITATION and not name.isdigit())


def _build_call_graph(sections: list[TheorySection],
                      drop_upto: int = _DROP_NAMES_UPTO,
                      derived: bool = False) -> CallGraph:
    """Single-pass scan building a full name-level call graph.

    Uses the shared filtering helpers (`_noise_ranges`,
    `_build_def_sites`): skips text/comment blocks, definition sites, and
    antiquotation-only mentions.  ``drop_upto`` is forwarded to
    :func:`_is_citation_name` — length-1 names (variable collisions) are
    excluded by default; see that function and ``--drop-names-upto``.

    ``derived`` treats Isabelle's definitional spellings (``foo_def``,
    ``foo_defs``) as citations of ``foo``.  Off by default, because the graph
    is over FACTS and ``foo_def`` is a different fact from ``foo``; only
    :func:`cmd_unused` turns it on, where the question is whether the
    DECLARATION is dead.  See the note there.
    """
    # 1. Collect candidate names (same filter as cmd_dead).  A name that is a
    #    proof method / attribute / keyword / numeral — or too short to tell
    #    from a term variable — is not a citable fact, so `by simp` and the
    #    universal variable `x` alike don't mint spurious edges.
    name_set: set[str] = set()
    for sec in sections:
        for e in sec.entries:
            if (e.tag in _CITABLE_TAGS
                    and e.name != "?" and _is_citation_name(e.name, drop_upto)):
                name_set.add(e.name)

    # 1b. Derived-fact spellings.  Isabelle mints `foo_def` from `definition
    #     foo`, and citing it IS a use of `foo` — often the only one, since an
    #     `equal` instance proof cites nothing but `equal_foo_def`.  The dotted
    #     families (`foo.simps`, `foo.induct`) need no help: the `[\w']+`
    #     tokeniser already splits them, leaving a bare `foo` to match.  The
    #     underscore family does not split, so map it back explicitly.
    derived_base: dict[str, str] = {}
    for n in (name_set if derived else ()):
        for suffix in ("_def", "_defs"):
            spelling = n + suffix
            # An entry genuinely named `foo_def` keeps its own identity; only
            # spellings that are not themselves entries are treated as derived.
            if spelling not in name_set:
                derived_base[spelling] = n

    # 2. Build def-site and text-block exclusion ranges.
    def_sites = _build_def_sites(sections, name_set)
    text_ranges = _noise_ranges(sections)

    # 3. Build line-to-entry index for caller attribution.
    line_index = _build_line_index(sections)

    # 4. Reference-extraction patterns.
    #    antiq_re strips doc antiquotations (@{thm foo}) so a name cited only
    #    in rendered documentation is not counted as a proof-body call.
    antiq_re = re.compile(r'@\{(?:text|thm|term|const)\s+["\']?\w+["\']?\}')
    #    The old per-name search matched a name wherever it sat between
    #    non-`[\w']` characters.  Because `\` (the start of a \<...> symbol)
    #    is itself non-`[\w']`, a name can match two ways, and we must
    #    extract both to reproduce every edge without inventing any:
    #      * sym_re — maximal runs that include \<...> symbol tokens, so a
    #        symbolic name like `merge_rt_F\<^sub>m` is one token (a plain
    #        [\w'] split would lose it);
    #      * word_re — maximal [\w'] runs, so a bare name that abuts a symbol
    #        (`iso_transaction` in `iso_transaction\<^sub>h`) is still found.
    #    Names with other non-identifier characters (beta-C-cor:3) are written
    #    double-quoted at the use site, so we also look up whole quoted
    #    spellings.  All three hashed into name_set are the linear-time
    #    equivalent of the per-name boundary search.
    sym_re = re.compile(r"(?:\\<\^?\w+>|[\w'])+")
    word_re = re.compile(r"[\w']+")
    quoted_re = re.compile(r'"([^"]+)"')

    # 5. Single linear pass: O(total source size), not O(lines x names).
    #    Tokenise each line once and intersect with the name set, rather
    #    than testing every one of ~10^5 names against the line.
    callers: dict[str, set[str]] = {n: set() for n in name_set}
    callees: dict[str, set[str]] = {}

    # Bind the per-line hot callables to locals: this loop runs once per source
    # line (millions of times), and a local is a fast LOAD_FAST vs an attribute
    # lookup on each.
    ns_inter = name_set.intersection
    derived_inter = set(derived_base).intersection
    antiq_sub = antiq_re.sub
    word_findall = word_re.findall
    sym_findall = sym_re.findall
    quoted_findall = quoted_re.findall

    for sec in sections:
        lines = sec.source()
        t_ranges = text_ranges.get(sec.theory, [])
        d_map = def_sites.get(sec.theory, {})
        idx = line_index.get(sec.theory, [])
        # Flatten the prose ranges into a 1-indexed line mask: a single O(1)
        # lookup per line replaces the old `any(line_no in r for r in t_ranges)`
        # rescan (~65M range tests at AFP scale).  Slice-assignment marks each
        # range C-side; the +2 pad keeps line_no == len(lines) in bounds.
        text_mask = _line_mask(len(lines),
                               ((r.start, r.stop - 1) for r in t_ranges))
        for line_no_0, line in enumerate(lines):
            line_no = line_no_0 + 1
            if text_mask[line_no]:
                continue
            # Strip doc antiquotations only when one is present; otherwise the
            # sub is a no-op that still scans the whole line.
            stripped = antiq_sub('', line) if '@{' in line else line
            # Candidate referenced names on this line.  word_re ([\w'] runs) is
            # always needed; sym_re differs from it only where a \<...> symbol
            # appears, and quoted_re only where a " does — so the two extra
            # findalls run on just those lines, not every line.  The union is
            # identical to scanning all three unconditionally (the oracle's
            # reference), but skips the provably-redundant passes.
            words = word_findall(stripped)
            cand = ns_inter(words)
            # `foo_def` resolves to `foo` (see derived_base).  Guarded on the
            # map being non-empty so the default path pays a truthiness test
            # rather than a set intersection on every line of every theory.
            if derived_base:
                dv = derived_inter(words)
                if dv:
                    cand = cand | {derived_base[d] for d in dv}
            if '\\<' in stripped:
                cand |= ns_inter(sym_findall(stripped))
            if '"' in stripped:
                cand |= ns_inter(quoted_findall(stripped))
            if not cand:
                continue
            caller_entry = _entry_at_line(idx, line_no)
            if caller_entry is not None and caller_entry.name == "?":
                continue
            # A citation outside every indexed entry is still a real use: the
            # span-bounding outer commands (`instance`, `lemmas`, `declare`,
            # `code_printing`, `export_code`) cite facts but declare nothing,
            # so they are not entries and own no lines.  Dropping their
            # citations makes the cited fact read as unused — an `equal`
            # instance proof is the whole reason its own `equal_*` definition
            # exists.  Attribute them to a synthetic per-theory top-level
            # caller so the edge exists and carries a location.
            caller_name = (caller_entry.name if caller_entry is not None
                           else f"{sec.theory}:<toplevel>")
            for name in cand:
                d_ranges = d_map.get(name)
                if d_ranges and any(line_no in r for r in d_ranges):
                    continue
                callers[name].add(caller_name)
                callees.setdefault(caller_name, set()).add(name)

    return CallGraph(callers=callers, callees=callees, all_names=name_set)


# A proof method is introduced by one of the three pure proof keywords
# `by` / `apply` / `proof`; the method name is the first token after it
# (optionally wrapped in an opening `(`).  Anchoring on the introducer is
# what makes the scan precise: the method namespace contains short,
# variable-colliding names (`N`, `order`, `field`, `split`, `all`), but in
# *introducer position* even a one-letter token is unambiguously the method.
# Trade-off: this counts the initial method of each `by`/`apply`/`proof`, so
# combinator-chained (`by (induct x) auto`) and line-wrapped methods are
# undercounted — never over-counted, which keeps the ranking trustworthy.
_METHOD_INTRO_RE = re.compile(r"\b(?:by|apply|proof)\b\s*\(?\s*([\w']+)")


def _scan_methods(sections: list[TheorySection], only: str | None = None,
                  ) -> tuple[Counter, list[tuple[str, int, "Entry | None", str]]]:
    """Tally proof-method uses across live theory source.

    Returns ``(counts, located)``:

    * ``counts`` — :class:`collections.Counter` ``{method: occurrences}`` over
      every ``by`` / ``apply`` / ``proof`` introducer on a *live* line (not a
      ``text \\<open>...\\<close>`` block, a ``\\<comment>`` annotation, or a
      per-entry preamble — so prose like "apply the rule" is not mined).
    * ``located`` — ``[(theory, line_no, owning_entry, line_text)]`` for the
      method named by ``only`` (empty when ``only`` is None), the method
      analogue of :func:`_find_callers`.

    This is the complement of the citation router: the tokens
    :func:`_is_citation_name` declines to treat as fact-graph edges are
    exactly the method uses surfaced here.
    """
    methods = _isa_ns.PROOF_METHODS
    counts: Counter = Counter()
    located: list[tuple[str, int, Entry | None, str]] = []
    line_index = _build_line_index(sections)
    intro_finditer = _METHOD_INTRO_RE.finditer
    for sec in sections:
        lines = sec.source()
        # "Live" = not inside a text block, multi-line \<comment>, or preamble
        # (the same notion `_grep_sections` uses), so an `apply`/`by` mentioned
        # in prose does not register as a method use.  A 1-indexed line mask
        # gives O(1) liveness per line, vs rescanning every noise range (the
        # same flattening the call-graph build uses).
        noise_mask = _line_mask(len(lines), _noise_spans(sec))
        idx = line_index.get(sec.theory, [])
        for line_no_0, line in enumerate(lines):
            line_no = line_no_0 + 1
            if noise_mask[line_no]:
                continue
            # The introducer regex requires one of these whole words, so its
            # letters must be present — a cheap necessary-condition guard skips
            # the regex on the many lines that hold no proof introducer at all.
            if 'by' not in line and 'apply' not in line and 'proof' not in line:
                continue
            hit_only = False
            for m in intro_finditer(line):
                tok = m.group(1)
                if tok in methods:
                    counts[tok] += 1
                    if tok == only:
                        hit_only = True
            if hit_only:
                located.append((sec.theory, line_no,
                                _entry_at_line(idx, line_no), line.rstrip()))
    return counts, located


def _bfs_depths(neighbors: Callable[[str], Iterable[str]],
                seeds: Iterable[str], *, seed_depth: int = 0) -> dict[str, int]:
    """Breadth-first shortest-path depths from `seeds`, over a graph given as a
    `neighbors(node) -> iterable of adjacent nodes` callback.

    Returns ``{node: depth}`` *including* the seeds, which sit at ``seed_depth``;
    each successive ring is one deeper.  The depth convention is the caller's,
    made explicit by ``seed_depth`` rather than baked in:

      * ``seed_depth=0`` — the seed is depth 0 (the entry-level call closures,
        ``callers -r`` / ``callees -r``, which pop the seed afterward).
      * ``seed_depth=-1`` — the seed is a phantom hop so its *direct* neighbours
        are depth 0 ("direct"), the import-graph convention (``deps -r`` /
        ``uses -r``, which pop the seed too).

    The callback — rather than a prebuilt map — is what lets one BFS serve both
    a stored adjacency (the call graph; reverse imports) and a *lazily resolved*
    one (forward imports, whose resolver records out-of-project edges as a side
    effect).  Level-synchronised with a visited guard, so it is safe on any
    graph (DAG or cyclic) and yields true shortest-path depth.
    """
    depths: dict[str, int] = {}
    frontier = list(seeds)
    depth = seed_depth
    while frontier:
        nxt: list[str] = []
        for node in frontier:
            if node in depths:
                continue
            depths[node] = depth
            nxt.extend(neighbors(node))
        frontier = nxt
        depth += 1
    return depths


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

def _format_extent(entry: Entry) -> str:
    """Format the `[src ...]` extent annotation for an entry.

    `src` is the entry's full span ``src_start..thy_end`` — a leading `text`
    preamble through the trailing blanks before the next entry.  The `body`
    span ``thy_line..body_end_line`` is surfaced separately whenever it is
    narrower at either end: a leading doc block (``src_start < thy_line``) or
    a trailing inter-lemma block (``body_end < thy_end``).  The body end is
    the safe cut boundary for `bin/move-block.py`; `src` is the
    end-of-region the next entry-or-section starts after.
    """
    if not entry.thy_line:
        return ""
    src_start = entry.src_start
    span_size = entry.line_count
    body_end = entry.body_end_line or entry.thy_end
    if src_start < entry.thy_line or body_end < entry.thy_end:
        body_size = body_end - entry.thy_line + 1
        return (f"[src {src_start}..{entry.thy_end}, "
                f"body {entry.thy_line}..{body_end}, "
                f"{body_size}/{span_size} lines]")
    return f"[src {src_start}..{entry.thy_end}, {span_size} lines]"


def _format_name_line(sec: TheorySection, entry: Entry) -> str:
    ext = _format_extent(entry)
    span = f" {ext}" if ext else ""
    return f"{entry.name} ({entry.tag}) — {sec.theory}{span}"


def _proof_extent(sec: TheorySection, proof_line: int, thy_end: int) -> int:
    """Walk forward from proof_line, return last line that belongs to the proof.
    Stops at `text \\<open>...` blocks, section headers, next declarations, or
    end of file.  Returns proof_line itself for one-line proofs.
    """
    lines = sec.source()
    last = proof_line
    for line_no in range(proof_line + 1, thy_end + 1):
        if line_no > len(lines):
            break
        cline = lines[line_no - 1]
        stripped = cline.strip()
        # Stop at top-level documentation blocks (text \<open>...\<close>) but
        # NOT at in-proof Isar annotations (\<comment> \<open>...\<close>), which
        # are routine inside proof bodies.
        if stripped.startswith("text ") or stripped.startswith("text\\<open>"):
            break
        if SECTION_RE.match(cline):
            break
        if DECL_RE.match(cline):
            break
        if stripped:
            last = line_no
    return last


def _is_latex_noise(line: str) -> bool:
    """Lines containing LaTeX figure/typesetting markup we want to skip in
    truncated previews of text blocks (e.g. UTM.thy's tikzpicture diagrams)."""
    return bool(LATEX_LINE_RE.search(line))


def _strip_text_wrapper(lines: list[str]) -> list[str]:
    """Strip leading `text \\<open>` / `text_raw \\<open>` and trailing
    `\\<close>` from a text block body, so previews don't show the wrapper.
    Returns a copy; does nothing if the markers aren't found.
    """
    if not lines:
        return lines
    out = list(lines)
    # Strip leading "text \<open>" or "text_raw \<open>"
    first = out[0]
    m = re.match(r"^(\s*)(?:text_raw|text)\s*\\<open>\s*(.*)$", first)
    if m:
        stripped_first = (m.group(1) + m.group(2)).rstrip()
        if stripped_first:
            out[0] = stripped_first
        else:
            out = out[1:]
    if not out:
        return out
    # Strip trailing "\<close>" from last line
    last = out[-1]
    if last.rstrip().endswith("\\<close>"):
        trimmed = last.rstrip()[: -len("\\<close>")].rstrip()
        if trimmed:
            out[-1] = trimmed
        else:
            out = out[:-1]
    return out


def _truncate_preview(lines: list[str], n: int,
                      skip_latex: bool = True) -> tuple[list[str], int]:
    """Return (preview_lines, omitted_count).  Picks up to N non-blank,
    non-LaTeX content lines from the start of `lines`.  `omitted_count` is
    how many *original* lines were not included in the preview.
    """
    if n <= 0:
        return [], len(lines)
    out = []
    consumed = 0
    for line in lines:
        consumed += 1
        if not line.strip():
            continue
        if skip_latex and _is_latex_noise(line):
            continue
        out.append(line)
        if len(out) >= n:
            break
    omitted = len(lines) - consumed
    return out, max(0, omitted)


def _render_preamble(sec: TheorySection, preamble: tuple[int, int],
                     mode: str, context: int) -> str:
    """Render a preamble text block.

    mode='summary': first `context` content lines + "[+N more preamble lines]"
    mode='full':    full slice, wrapper stripped
    """
    start, end = preamble
    body = _strip_text_wrapper(sec.slice(start, end))
    block_size = len(body)
    if mode == "full":
        return "\n".join(body)
    preview, _ = _truncate_preview(body, context)
    suffix = ""
    shown = len(preview)
    remaining = block_size - shown
    if remaining == 1:
        return "\n".join(body)
    if remaining > 0:
        suffix = (f"\n  [+{remaining} more preamble lines, "
                  f"use --comments-only or -V to see]")
    return "\n".join(preview) + suffix


def _render_roadmap(roadmap: list[tuple[int, str]], context: int,
                    proof_remaining: int, mode: str) -> str:
    """Render a proof roadmap (extracted \\<comment> annotations).

    mode='summary': first `context` annotations + "...(N total of M proof lines)"
    mode='full':    all annotations
    """
    if not roadmap:
        # Fallback: show the existing "+N more proof lines" count line.
        if proof_remaining > 0:
            return (f"  [+{proof_remaining} more proof line"
                    f"{'s' if proof_remaining != 1 else ''}]")
        return ""
    if mode == "full":
        shown = roadmap
    else:
        shown = roadmap[:max(1, context)]
    out = []
    for ln, content in shown:
        out.append(f"  | line {ln}: {content}")
    if mode != "full" and len(roadmap) > len(shown):
        rest = len(roadmap) - len(shown)
        if rest == 1:
            ln, content = roadmap[len(shown)]
            out.append(f"  | line {ln}: {content}")
        else:
            out.append(f"  | ...({rest} more annotations "
                       f"in {proof_remaining}-line proof, use -U N to see more)")
    return "\n".join(out)


def _statement_text(sec: TheorySection, entry: Entry) -> str:
    """The entry's statement slice as one string: the declaration lines
    [thy_line..decl_end_line] (the lemma/def statement, not the proof).

    Falls back to `entry.text` for entries without a source location (e.g.
    an AXIOM placeholder), matching how `render_entry` degrades — so a
    statement search still sees *something* for those.
    """
    if not entry.thy_line:
        return entry.text
    return "\n".join(sec.slice(entry.thy_line, entry.decl_end_line))


def render_entry(sec: TheorySection, entry: Entry, *,
                 verbatim: bool = False,
                 statement: bool = False,
                 comments: str = "on",
                 context: int = 2) -> str:
    """Render a single entry.

    statement:       just the declaration slice [thy_line..decl_end_line]
                     (the statement, no proof) — the narrowest view
    verbatim:        full source slice [thy_line..thy_end]
    comments='on':   preamble (truncated) + header + statement + proof preview
                     + roadmap (truncated)
    comments='off':  header + statement + proof preview only (current default)
    comments='only': preamble (full) + header + roadmap (full), no statement
    context:         lines of preamble preview / roadmap entries shown

    `statement` and `verbatim` are opposite ends of the slice spectrum
    (declaration-only vs declaration+proof); `show` declares them mutually
    exclusive at the CLI.  If both somehow arrive, the narrower one wins.
    """
    ext = _format_extent(entry)
    header = f"--- {entry.name} ({entry.tag}) — {sec.theory}.thy {ext} ---"

    # No source location (e.g. AXIOM placeholder) → fall back to entry.text
    if not entry.thy_line:
        return f"{header}\n{entry.text}"

    if statement:
        body_lines = sec.slice(entry.thy_line, entry.decl_end_line)
        return header + "\n" + "\n".join(body_lines)

    if verbatim:
        body_lines = sec.slice(entry.thy_line, entry.thy_end)
        return header + "\n" + "\n".join(body_lines)

    out_parts: list[str] = []

    # Preamble (above header)
    if comments != "off" and entry.preamble:
        pmode = "full" if comments == "only" else "summary"
        rendered = _render_preamble(sec, entry.preamble, pmode, context)
        if rendered:
            pstart, pend = entry.preamble
            out_parts.append(f"--- preamble [{pstart}-{pend}] ---")
            out_parts.append(rendered)
            out_parts.append("")

    out_parts.append(header)

    if comments == "only":
        # Skip statement + proof; show only roadmap (full).
        if entry.roadmap:
            out_parts.append("--- roadmap (\\<comment> annotations) ---")
            proof_end = _proof_extent(sec, entry.proof_line, entry.thy_end) \
                if entry.proof_line else entry.thy_end
            out_parts.append(_render_roadmap(entry.roadmap, context,
                                             proof_end - entry.proof_line, "full"))
        elif not entry.preamble:
            out_parts.append("(no comment context for this entry)")
        return "\n".join(out_parts)

    # Statement + proof preview
    if entry.proof_line and entry.proof_line >= entry.decl_end_line:
        statement = sec.slice(entry.thy_line, entry.decl_end_line)
        first_proof = sec.slice(entry.proof_line, entry.proof_line)
        proof_end = _proof_extent(sec, entry.proof_line, entry.thy_end)
        remaining = max(0, proof_end - entry.proof_line)
        out_parts.append("\n".join(statement + first_proof))
        if comments != "off" and entry.roadmap:
            out_parts.append(_render_roadmap(entry.roadmap, context,
                                             remaining, "summary"))
        elif remaining == 1:
            extra = sec.slice(entry.proof_line + 1, entry.proof_line + 1)
            out_parts.append("\n".join(extra))
        elif remaining > 0:
            out_parts.append(f"  [+{remaining} more proof lines]")
    else:
        # No proof captured → just the declaration as recorded by the parser.
        body_lines = sec.slice(entry.thy_line, entry.decl_end_line)
        out_parts.append("\n".join(body_lines))

    return "\n".join(out_parts)


# ---------------------------------------------------------------------------
# Verbosity-mode dispatch
# ---------------------------------------------------------------------------

def _emit_matches(sections_by_theory: dict[str, TheorySection],
                  matches: list[Entry], pattern: str, flags: "CmdFlags",
                  *, statement: bool = False) -> None:
    # `statement` is the *render* selector (declaration-only).  It is passed
    # explicitly rather than read off `flags` so it stays a `show` concern:
    # on `find`, `flags.statement` means "match the statement slice", which
    # must not bleed into how the matched entries are rendered.
    if not matches:
        print(f"No entries matching '{pattern}'.")
        return

    if flags.mode == "count":
        print(len(matches))
        return

    if flags.mode == "names":
        for e in matches:
            print(_format_name_line(sections_by_theory[e.theory], e))
        return

    if flags.mode == "all":
        for e in matches:
            print(render_entry(sections_by_theory[e.theory], e,
                               verbatim=flags.verbatim,
                               statement=statement,
                               comments=flags.comments,
                               context=flags.context))
            print()
        return

    # mode == "first"
    e0 = matches[0]
    print(render_entry(sections_by_theory[e0.theory], e0,
                       verbatim=flags.verbatim,
                       statement=statement,
                       comments=flags.comments,
                       context=flags.context))
    if len(matches) > 1:
        print()
        print(f"[+{len(matches) - 1} more match(es).  Use --all to show, "
              f"--names for a list, --count for just the count.]")


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def cmd_summary(sections: list[TheorySection]) -> None:
    total = sum(len(s.entries) for s in sections)
    print("# Theory Index\n")
    print(f"{total} entries across {len(sections)} theories  "
          f"(parsed live from .thy files)\n")
    print("## Theories\n")
    print("Source-line counts (`.thy` file size), entry counts, and key exports.\n")
    print("| Theory | Src | D | L | T | Key Exports |")
    print("|--------|----:|--:|--:|--:|-------------|")
    for sec in sections:
        defs = [e for e in sec.entries if e.tag in _DEFINITION_TAGS]
        lemmas = [e for e in sec.entries if e.tag == "LEMMA"]
        thms = [e for e in sec.entries if e.tag == "THEOREM"]

        key_names: list[str] = []
        for e in defs:
            if e.name != "?" and e.name not in key_names:
                key_names.append(e.name)
        for e in thms:
            if e.name != "?" and e.name not in key_names:
                key_names.append(e.name)
        if not key_names:
            for e in lemmas[:3]:
                if e.name != "?" and e.name not in key_names:
                    key_names.append(e.name)

        exports = ", ".join(key_names[:6])
        if len(key_names) > 6:
            exports += ", ..."

        print(f"| {sec.theory} | {sec.thy_lines} | "
              f"{len(defs)} | {len(lemmas)} | {len(thms)} | {exports} |")


def _resolve_theory(sections: list[TheorySection], name: str) -> TheorySection | None:
    """Resolve a theory by path or by name.

    Two argument forms, so callers can paste either a file path or a
    bare theory name:

      - **Path form** — the argument carries a path separator or a
        ``.thy`` suffix (e.g. ``sub/Foo.thy``).
        Matched against each section's resolved path, so symlinks and
        relative/absolute spellings all land on the same section.
      - **Name form** — a bare theory name (e.g.
        ``Foo``), matched against the section's theory
        name (exact, then case-insensitive).  This is the convenience
        spelling: the name is looked up among the sections already
        discovered through the ``common.py`` ROOT-walking routines.
    """
    if name.endswith(".thy") or "/" in name:
        try:
            target = Path(name).resolve()
        except OSError:
            target = None
        if target is not None:
            for s in sections:
                if s.path.resolve() == target:
                    return s
        # Path that doesn't match a known section: fall back to its
        # stem so `path/to/Foo.thy` still resolves to theory `Foo`.
        stem = Path(name).stem
        for s in sections:
            if s.theory == stem:
                return s
        return None
    for s in sections:
        if s.theory == name:
            return s
    for s in sections:
        if s.theory.lower() == name.lower():
            return s
    return None


def _suggest_theory(sections: list[TheorySection], name: str) -> str | None:
    """Closest theory to `name`, as a cwd-relative `.thy` path suggestion
    for a 'did you mean ...?' hint; None if nothing is close.

    Matches on the theory *stem*, so a mistyped path
    (`path/to/Fooo.thy`) is handled like a bare name (`Fooo`)."""
    import difflib
    by_name = {s.theory: s for s in sections}
    matches = difflib.get_close_matches(
        Path(name).stem, list(by_name), n=1, cutoff=0.6)
    if not matches:
        return None
    sec = by_name[matches[0]]
    try:
        return str(sec.path.relative_to(Path.cwd()))
    except ValueError:
        return str(sec.path)


def _resolve_conjunct(sections: list[TheorySection], name: str) -> str | None:
    """If `name` is a named conjunct of a multi-`shows` lemma, return the
    parent lemma name; else None.  Lets callers/callees/show resolve a
    conjunct to the entry that bundles it."""
    for sec in sections:
        for e in sec.entries:
            if name in e.conjuncts:
                return e.name
    return None


def cmd_theory(sections: list[TheorySection], name: str,
               flags: "CmdFlags") -> None:
    sec = _resolve_theory(sections, name)
    if sec is None:
        print(f"Theory '{name}' not found.  Known theories:")
        for s in sorted(sections, key=lambda x: x.theory):
            print(f"  {s.theory}")
        return

    # Terse modes: the theory's namespace as a bare list, no header or
    # code-fence decoration, so output is greppable / scriptable.
    if flags.mode == "count":
        print(len(sec.entries))
        return
    if flags.mode == "names":
        for e in sec.entries:
            print(_format_name_line(sec, e))
        return

    print(f"## {sec.theory}.thy  ({sec.thy_lines} src lines, {len(sec.entries)} entries)")
    if flags.verbatim:
        for e in sec.entries:
            print()
            print(render_entry(sec, e, verbatim=True))
        return

    # Default: pre-formatted entries, optionally with preamble headers
    print("```")
    for e in sec.entries:
        if flags.comments != "off" and e.preamble:
            ps, pe = e.preamble
            body = _strip_text_wrapper(sec.slice(ps, pe))
            preview, _ = _truncate_preview(body, flags.context)
            if preview:
                print()
                print(f"[preamble {ps}-{pe}]: " + " ".join(
                    line.strip() for line in preview))
        print(e.text)
    print("```")


def cmd_find(sections: list[TheorySection], pattern: str,
             flags: "CmdFlags") -> None:
    # Shell users often reach for grep-style escaped alternation
    # ('a\|b\|c'); in Python's re, '\|' is the literal '|' character,
    # which would silently match nothing.  Preprocess to PCRE-style
    # alternation so the pattern does what the user expects.
    pattern = pattern.replace(r"\|", "|")
    pat = re.compile(pattern, re.IGNORECASE)
    by_theory = _sections_by_theory(sections)
    matches: list[Entry] = []
    if flags.statement:
        # Statement-slice search: match the regex against the declaration
        # text (the lemma/def statement, not the proof body) — a token-level
        # approximation of `find_theorems` ("which entries are *stated about*
        # this", whatever they're named).  Not term/type-aware.
        for s in sections:
            for e in s.entries:
                if pat.search(_statement_text(s, e)):
                    matches.append(e)
    else:
        for s in sections:
            for e in s.entries:
                if pat.search(e.name):
                    matches.append(e)
                elif any(pat.search(c) for c in e.conjuncts):
                    matches.append(e)  # matched via a named `shows` conjunct

    # `--statement` here selects the match locus, not the render: show the
    # matched entries the usual way (statement + proof preview).
    _emit_matches(by_theory, matches, pattern, flags)

    if flags.with_comments:
        # Additionally search inside preamble bodies and roadmap content,
        # producing context windows.
        comment_hits = _find_in_comments(sections, pat, flags.context)
        if comment_hits:
            print()
            print(f"--- comment matches for '{pattern}' "
                  f"({len(comment_hits)} hit(s)) ---")
            for hit in comment_hits:
                print(hit)


def _find_in_comments(sections: list[TheorySection], pat: re.Pattern,
                      context: int) -> list[str]:
    """Search inside text blocks and \\<comment> annotations across all
    theories.  Returns formatted hit strings: filename:line + context window.
    """
    hits: list[str] = []
    for sec in sections:
        src = sec.source()
        # Text blocks (preambles + standalone)
        for tb_start, tb_end in sec.text_blocks:
            for ln in range(tb_start, tb_end + 1):
                if ln > len(src):
                    break
                line = src[ln - 1]
                if pat.search(line):
                    lo = max(tb_start, ln - context)
                    hi = min(tb_end, ln + context)
                    snippet = src[lo - 1:hi]
                    hits.append(f"\n{sec.theory}.thy:{ln} "
                                f"(in text block {tb_start}..{tb_end}):")
                    for j, snippet_line in enumerate(snippet, start=lo):
                        marker = ">" if j == ln else " "
                        hits.append(f"  {marker} {j}: {snippet_line}")
        # Inline \<comment> annotations: each entry's roadmap
        for e in sec.entries:
            for ln, content in e.roadmap:
                if pat.search(content):
                    hits.append(f"\n{sec.theory}.thy:{ln} "
                                f"(\\<comment> in {e.name}): {content}")
    return hits


def cmd_show(sections: list[TheorySection], name: str,
             flags: "CmdFlags") -> None:
    by_theory = _sections_by_theory(sections)
    matches: list[Entry] = []
    for s in sections:
        for e in s.entries:
            if e.name == name:
                matches.append(e)
    if not matches:
        for s in sections:
            for e in s.entries:
                if e.name.lower() == name.lower():
                    matches.append(e)
    if not matches:
        # Conjunct fallback (before substring): NAME may be a named conjunct
        # of a multi-`shows` lemma; resolve to the parent that bundles it.
        for s in sections:
            for e in s.entries:
                if name in e.conjuncts:
                    matches.append(e)
        if matches:
            parents = ", ".join(sorted({e.name for e in matches}))
            print(f"# '{name}' is a named conjunct of {parents}:")
    if not matches:
        # Substring fallback
        for s in sections:
            for e in s.entries:
                if name.lower() in e.name.lower():
                    matches.append(e)
    # On `show`, `--statement` is the render selector: declaration only.
    _emit_matches(by_theory, matches, name, flags, statement=flags.statement)


def cmd_defs(sections: list[TheorySection], theory: str,
             flags: "CmdFlags") -> None:
    sec = _resolve_theory(sections, theory)
    if sec is None:
        print(f"Theory '{theory}' not found.")
        return
    matches = [e for e in sec.entries if e.tag in _DEFINITION_TAGS]
    if not matches:
        print(f"No definitions found in '{sec.theory}'.")
        return
    if flags.mode == "count":
        print(len(matches))
        return
    if flags.mode == "names":
        for e in matches:
            print(_format_name_line(sec, e))
        return
    for e in matches:
        print(render_entry(sec, e))
        print()


def _resolve_import(imp: str, sec_by_name: dict[str, TheorySection]) -> str | None:
    """Map a raw ``imports``-clause token to the bare in-project theory it
    denotes, or ``None`` if it is external.

    `parse_thy_imports` returns tokens verbatim, but the section index
    (`sec_by_name`) is keyed by **bare** theory name.  Same-session imports
    are written bare (``Substrate``) and match directly; cross-session
    imports are session-qualified (``NDTHT_Base.Substrate``) and resolve by
    their tail after the last ``.``.  A genuinely external import
    (``HOL-Library.FuncSet``) names no in-project theory by either spelling,
    so it stays ``None`` and the caller keeps the *raw* token for the
    ``[out-of-project]`` line.

    Tail-matching is correct for every realistic tree: an external leaf-name
    (``FuncSet``, ``List``) does not collide with a project theory name.  The
    one case it cannot distinguish — an external ``Sess.Foo`` whose tail
    equals an in-project ``Foo`` and whose ``Sess`` is *not* an in-project
    session — is a name collision, the province of `[disambig-names]`; if it
    ever arises, gate the tail-match on the qualifier naming a known session
    (`SessionInfo.name`)."""
    if imp in sec_by_name:
        return imp
    if "." in imp:
        tail = imp.rsplit(".", 1)[1]
        if tail in sec_by_name:
            return tail
    return None


def cmd_deps(sections: list[TheorySection], theory: str,
             reverse: bool = False, recursive: bool = False) -> None:
    """Theory-level (not entry-level) import dependencies.

    Forward (``reverse=False``): the theories this one imports.
    Reverse (``reverse=True``): the theories that import this one.
    Exposed as the ``deps`` (forward) / ``uses`` (reverse) subcommand
    pair — the theory-graph analogue of the entry-level
    ``callees`` / ``callers`` pair (brew's ``deps`` / ``uses``
    convention).

    Direct by default; ``recursive`` (``-r``) gives the transitive
    closure with per-hop depth labels — matching the direct/``-r``
    semantics of the entry-level pair."""
    target = _resolve_theory(sections, theory)
    if target is None:
        print(f"Theory '{theory}' not found.")
        return

    by_theory = _sections_by_theory(sections)

    def emit(found: dict[str, int]) -> None:
        for name, depth in sorted(found.items(), key=lambda kv: (kv[1], kv[0])):
            sec = by_theory[name]
            tag = "  [direct]" if depth == 0 else f"  [depth {depth}]"
            print(f"  {name}  ({sec.thy_lines} src lines, "
                  f"{len(sec.entries)} entries){tag}")

    scope = "transitively" if recursive else "directly"

    if reverse:
        # Invert the in-project import adjacency: child -> theories that
        # import the child.  The reverse direction needs the whole graph
        # regardless of depth, so the full scan here is unavoidable.
        rev: dict[str, list[str]] = {s.theory: [] for s in sections}
        for s in sections:
            for imp in parse_thy_imports(s.path):
                resolved = _resolve_import(imp, by_theory)
                if resolved is not None:
                    rev[resolved].append(s.theory)
        if recursive:
            found = _bfs_depths(lambda n: rev.get(n, []), [target.theory],
                                seed_depth=-1)
            found.pop(target.theory, None)
        else:
            found = {name: 0 for name in rev.get(target.theory, [])}
        if not found:
            print(f"No in-project theory imports {target.theory} ({scope}).")
            return
        print(f"Theories that import {target.theory} ({scope}):")
        emit(found)
        return

    # Forward.  Direct: just the target's own import line.  Recursive:
    # lazy BFS over the imports graph.  Out-of-project imports (e.g.
    # HOL-Library.*) are direct edges, so they show in both modes.
    in_project: dict[str, int] = {}  # name -> depth (0 = direct import)
    out_of_project: set[str] = set()
    if recursive:
        def imports_of(name: str) -> list[str]:
            sec = by_theory.get(name)
            if sec is None:
                return []
            children: list[str] = []
            for imp in parse_thy_imports(sec.path):
                child = _resolve_import(imp, by_theory)
                if child is None:
                    out_of_project.add(imp)
                else:
                    children.append(child)
            return children
        in_project = _bfs_depths(imports_of, [target.theory], seed_depth=-1)
        in_project.pop(target.theory, None)
    else:
        for imp in parse_thy_imports(target.path):
            resolved = _resolve_import(imp, by_theory)
            if resolved is None:
                out_of_project.add(imp)
            elif resolved != target.theory:
                in_project[resolved] = 0

    if not in_project and not out_of_project:
        print(f"{target.theory} has no upstream dependencies.")
        return

    header = ("Import-transitive dependencies" if recursive
              else "Direct imports")
    print(f"{header} of {target.theory}:")
    emit(in_project)
    for name in sorted(out_of_project):
        print(f"  {name}  [out-of-project]")


def cmd_outline(sections: list[TheorySection], theory: str,
                flags: "CmdFlags") -> None:
    sec = _resolve_theory(sections, theory)
    if sec is None:
        print(f"Theory '{theory}' not found.")
        return

    items: list[tuple[int, str, object]] = []
    for level, title, ln in sec.outline:
        items.append((ln, "section", (level, title)))
    for e in sec.entries:
        if e.thy_line > 0:
            items.append((e.thy_line, "entry", e))
    if flags.comments != "off":
        for tb_start, tb_end in sec.text_blocks:
            items.append((tb_start, "text", (tb_start, tb_end)))
    items.sort(key=lambda x: x[0])

    if not items:
        print(f"No outline data for '{sec.theory}'.")
        return

    print(f"Outline of {sec.theory}.thy:\n")
    for ln, kind, payload in items:
        if kind == "section":
            level, title = payload  # type: ignore[misc]
            indent = {"chapter": "", "section": "", "subsection": "  ",
                      "subsubsection": "    "}[level]
            print(f"{indent}{level:>14}: {title}  (line {ln})")
        elif kind == "text":
            tb_start, tb_end = payload  # type: ignore[misc]
            block_size = tb_end - tb_start + 1
            body = _strip_text_wrapper(sec.slice(tb_start, tb_end))
            preview, _ = _truncate_preview(body, flags.context)
            preview_text = " ".join(line.strip() for line in preview)
            if len(preview_text) > 100:
                preview_text = preview_text[:97] + "..."
            print(f"        text     [{tb_start}..{tb_end}, {block_size} lines]: "
                  f"{preview_text}")
        else:
            e: Entry = payload  # type: ignore[assignment]
            size = e.line_count
            print(f"        {e.tag:<8} {e.name}  ({e.src_start}..{e.thy_end}, {size} lines)")


def _find_callers(sections: list[TheorySection], name: str,
                   external: bool = False,
                   ) -> list[tuple[str, int, str]]:
    """Find proof-body usages of *name* across all .thy files.

    Returns a list of (theory_name, line_no, line_text) triples, filtering
    out:
      - The definition site itself (same theory, within the entry's span).
      - Lines inside ``text \\<open>...\\<close>`` blocks (prose, not proof).
      - Antiquotation-only mentions: ``@{text name}``, ``@{thm name}``,
        ``@{term name}`` where the *only* occurrence of *name* on the line
        is inside an antiquotation.

    When ``external`` is true, additionally skip every line in the
    theory(ies) that define *name* — useful for "is anything outside
    Foo using Foo's primitives?" audits where intra-theory
    cross-references are noise.
    """
    word_re = re.compile(_isa_word_pattern(name))
    # Antiquotation pattern: @{text/thm/term/const "?name"?}
    antiq_re = re.compile(
        r'@\{(?:text|thm|term|const)\s+["\']?' + re.escape(name) + r'["\']?\}')

    # Shared infrastructure: per-theory def-site ranges (for `name`) and
    # text-block ranges (prose to skip).
    all_def_sites = _build_def_sites(sections, {name})
    def_theories: set[str] = {th for th, m in all_def_sites.items() if m}
    text_ranges = _noise_ranges(sections)

    results: list[tuple[str, int, str]] = []
    for sec in sections:
        # External mode: skip every line in the defining theory(ies),
        # treating intra-theory cross-references as noise.
        if external and sec.theory in def_theories:
            continue
        lines = sec.source()
        t_ranges = text_ranges.get(sec.theory, [])
        d_ranges = all_def_sites.get(sec.theory, {}).get(name, set())
        for line_no_0, line in enumerate(lines):
            line_no = line_no_0 + 1
            if not word_re.search(line):
                continue
            # Skip definition site.
            if any(line_no in r for r in d_ranges):
                continue
            # Skip text blocks.
            if any(line_no in r for r in t_ranges):
                continue
            # Skip if the only occurrences are inside antiquotations.
            stripped = antiq_re.sub('', line)
            if not word_re.search(stripped):
                continue
            results.append((sec.theory, line_no, line.rstrip()))
    return results


def _render_graph_results(sections: list[TheorySection],
                          reachable: dict[str, int],
                          label: str, seed: str,
                          flags: 'CmdFlags') -> None:
    """Shared rendering for callers -r and uses -r."""
    if flags.mode == "count":
        print(len(reachable))
        return
    if not reachable:
        print(f"No {label}s found for '{seed}'.")
        return

    # Build name → (theory, Entry) lookup for rendering.
    by_name = _entry_by_name(sections)

    if flags.mode == "names":
        for name in sorted(reachable):
            if name in by_name:
                thy, e = by_name[name]
                print(f"  {name} ({e.tag}) — {thy}")
            else:
                print(f"  {name}")
        return

    print(f"{len(reachable)} transitive {label}(s) of {seed}:\n")
    for name, depth in sorted(reachable.items(), key=lambda x: (x[1], x[0])):
        indent = "  " * (depth + 1)
        if name in by_name:
            thy, e = by_name[name]
            print(f"{indent}{name} ({e.tag}) — {thy} [L{e.thy_line}]")
        else:
            print(f"{indent}{name}")


def _enclosing_entry(sec: TheorySection, line_no: int) -> Entry | None:
    """Return the entry whose [src_start, thy_end] span contains *line_no*.

    Used by ``cmd_callers`` to annotate each hit with its enclosing lemma
    name — answering "which proof is calling this?" in one line rather
    than requiring a follow-up ``show`` invocation — and by ``cmd_enclosing``
    as the span-containment lookup behind ``query enclosing FILE:LINE``.  The
    span starts at ``src_start`` so a line in a leading doc block resolves to
    the entry it documents (not the preceding one).
    """
    for e in sec.entries:
        if e.thy_line and e.thy_end and e.src_start <= line_no <= e.thy_end:
            return e
    return None


def _owner_field(owner: Entry | None, span: bool = True) -> str:
    """The owning-entry column for a located hit — ``name (TAG) lo..hi`` (or
    ``—`` when the line has no owner).

    The single chokepoint for owner rendering, so name/tag/no-owner handling
    can't drift between commands.  ``span`` is the one *content* choice that
    legitimately differs by command, so it is a parameter rather than baked
    in:

      * `callers` / `methods` keep it (the default) — the next move after
        "who references X" is usually to open the owning lemma, so its
        ``lo..hi`` extent is the next locus, right there;
      * `grep` opts out (``span=False``) — a search hit is *already* a
        precise locus (its own matched line), so the owner's whole-lemma
        span is constant across the lemma's hits, repetitive, and would blur
        a content search into a line-owner report.
    """
    if owner is None or owner.name == "?":
        return "—"
    if span and owner.thy_line and owner.thy_end:
        return f"{owner.name} ({owner.tag}) {owner.src_start}..{owner.thy_end}"
    return f"{owner.name} ({owner.tag})"


def _parse_locus(token: str) -> tuple[str, int, int | None] | None:
    """Split a ``FILE:LINE`` or ``FILE:A..B`` locus into ``(file, lo, hi)``.

    The line part is handed to `_parse_line_range`, so a single ``:LINE``
    yields ``lo == hi`` and a ``:A..B`` range yields the inclusive span —
    the *same* ``A..B`` grammar `lines` accepts (including the open ``:A..``
    form, whose ``hi`` comes back ``None`` for the caller to resolve to EOF).
    That is the round-trip
    that makes a span printed elsewhere paste back in as a locus.  The file
    is split off on the *last* colon (``rpartition``), so a path that itself
    has no colon keeps its separators: ``sub/Foo.thy:8..12`` ->
    ``("sub/Foo.thy", 8, 12)``, ``Foo:42`` -> ``("Foo", 42, 42)``.

    A single trailing ``:`` or ``-`` is peeled off first: that is
    ripgrep's match(``:``)/context(``-``) marker, which `callers` and a
    real ``rg -n`` / ``grep -n`` both emit, so tolerating it lets the
    tool's own location output (and any grep paste-in) round-trip into
    `enclosing`.  Returns None when there is no ``:LINE`` suffix or the
    line part is not a valid range, so the caller reports the malformed
    locus and carries on instead of aborting the whole batch.
    """
    if token[-1:] in ":-":
        token = token[:-1]
    file_token, sep, span = token.rpartition(":")
    if not sep or not file_token or not span:
        return None
    try:
        lo, hi = _parse_line_range(span)
    except ValueError:
        return None
    return file_token, lo, hi


def _locus_role(entry: Entry, line_no: int) -> str:
    """Where in *entry* a line sits: 'in preamble', 'in proof', 'in
    statement', or ''.

    Uses the same `proof_line` / `decl_end_line` boundaries the renderer
    slices on, so the answer matches what `show --statement` vs the proof
    preview would show.  A line before the declaration (`line_no <
    thy_line`) is in the entry's leading doc block — 'in preamble'.  Empty
    for the rare inter-region line (a blank between a statement and its
    proof, or trailing text on a def).  The point during a build chase:
    knowing the failing line is the *statement* vs a *proof step* tells you
    which to edit.
    """
    if entry.thy_line and line_no < entry.thy_line:
        return "in preamble"
    if entry.proof_line and line_no >= entry.proof_line:
        return "in proof"
    if entry.decl_end_line and line_no <= entry.decl_end_line:
        return "in statement"
    return ""


# --- proof-internal block drill-down (enclosing) -------------------------
#
# `enclosing` resolves a line to its owning entry; inside a large structured
# proof the *nearest enclosing syntactic block* (the innermost
# `proof ... qed` / `{ ... }` the line sits in, as a pasteable `A..B` range)
# is the more useful answer — often a handful of lines rather than a
# 500-line lemma.  We find it by a lightweight, on-demand scan of *just* the
# one resolved entry's proof body — no index/Entry bloat, paid only when a
# drill-down is asked for.  Deliberately conservative: openers/closers are
# anchored at line start, so a `proof`/`qed`/`{` buried in a term string or
# a mid-line set-comprehension is ignored, and only *live* lines are read
# (comment / text blocks skipped).  If the open/close stack ever goes
# unbalanced the scan returns None and the caller falls back to the
# entry-level answer rather than emit a span it isn't sure of.
_GOAL_INTRO_RE = re.compile(
    r"^(have|show|hence|thus|obtain|consider)\b"
    r"(?:\s+([A-Za-z][\w'.]*)\s*:)?")
_PROOF_OPEN_RE = re.compile(r"^proof\b")
_QED_RE = re.compile(r"^qed\b")
# Line-anchored proof *terminators* (a goal proved without opening a block):
# clears the pending goal so its label can't leak onto a later `proof`.
_TERMINAL_RE = re.compile(r"^(by|done|sorry|oops)\b|^\.\.?\s*$")


@dataclass(frozen=True)
class _Block:
    """A nested proof block — a `proof..qed` or a raw `{..}` — labelled by
    the goal that introduces it.  `start`/`end` are 1-indexed inclusive, so
    `theory:start..end` is a locus that pastes into `lines` / `enclosing`."""
    kw: str        # introducing keyword (have/show/...) or "{" for a brace block
    name: str      # the goal's label (`key` of `have key:`); "" if anonymous
    start: int
    end: int


def _block_label(b: _Block) -> str:
    return "{ }" if b.kw == "{" else f"{b.kw} {b.name}".strip()


def _block_field(b: _Block) -> str:
    """`label start..end` — one breadcrumb element; the span round-trips."""
    return f"{_block_label(b)} {b.start}..{b.end}"


def _proof_blocks(sec: TheorySection, entry: Entry) -> list[_Block] | None:
    """Nested blocks inside *entry*'s proof, or None if the scan went
    unbalanced (caller then falls back to the entry-level answer).

    The lemma's own outermost `proof` is *not* reported: it is what the
    entry already represents.  Only blocks strictly inside it — nested
    `have ... proof ... qed`, raw `{ ... }` — are, since those are the
    narrower ranges a drill-down is for.
    """
    if not entry.proof_line:
        return []
    lines = sec.source()
    end = min(entry.body_end_line or entry.thy_end or len(lines), len(lines))
    noise = [range(lo, hi + 1) for lo, hi in _noise_spans(sec)]
    stack: list[tuple[str, str, int]] = []    # (kw, name, start)
    blocks: list[_Block] = []
    pending: tuple[str, str, int] | None = None   # a goal awaiting its proof
    main_open = False
    for ln in range(entry.proof_line, end + 1):
        if any(ln in r for r in noise):
            continue
        stripped = lines[ln - 1].strip()
        if not stripped:
            continue
        gm = _GOAL_INTRO_RE.match(stripped)
        if gm:
            pending = (gm.group(1), gm.group(2) or "", ln)
        if _PROOF_OPEN_RE.match(stripped):
            if not main_open and not stack:
                stack.append(("__main__", "", ln))   # the entry's own proof
                main_open = True
            else:
                stack.append(pending or ("proof", "", ln))
            pending = None
        elif _QED_RE.match(stripped):
            if not stack:
                return None
            kw, name, start = stack.pop()
            if kw != "__main__":
                blocks.append(_Block(kw, name, start, ln))
            pending = None
        elif stripped == "{":
            stack.append(("{", "", ln))
        elif stripped == "}":
            if not stack:
                return None
            kw, name, start = stack.pop()
            if kw != "__main__":
                blocks.append(_Block(kw, name, start, ln))
            pending = None
        elif _TERMINAL_RE.match(stripped):
            pending = None
    return None if stack else blocks


def _enclosing_blocks(blocks: list[_Block], line_no: int) -> list[_Block]:
    """Blocks containing *line_no*, outermost first — so the last element is
    the nearest (innermost) enclosing block."""
    containing = [b for b in blocks if b.start <= line_no <= b.end]
    containing.sort(key=lambda b: (b.start, -b.end))
    return containing


def cmd_enclosing(sections: list[TheorySection], loci: list[str],
                  block_mode: str = "nearest") -> None:
    """Report which entry encloses each ``FILE:LINE`` (or ``FILE:A..B``)
    locus — inverse of `outline`.

    A build failure surfaces a bare ``file:line``; the first triage move is
    naming the lemma that owns it.  This is a span-containment lookup over
    the same ``[thy_line, thy_end]`` spans `outline` prints, so unlike a
    ``^lemma ``-only ``awk`` scan it also names `definition` / `fun` /
    `datatype` owners.  A range locus (``FILE:A..B`` — e.g. a diff hunk or a
    multi-line error) lists *every* entry whose span overlaps it, the
    "which lemmas does this hunk touch" question.  Each result prints one
    ``LOCUS -> OWNER`` line (the location is the house ``theory:line`` form,
    so it round-trips back into `enclosing` / `lines` / an editor); malformed
    or unresolved loci report to stderr and do not stop the batch.

    For a single line inside a proof, ``block_mode`` drills past the entry to
    the enclosing *syntactic block* — the narrow range a build error really
    sits in, appended as ``▸ have key 3705..3740`` (itself a pasteable span):
      * ``"nearest"`` (default) — the innermost enclosing block, or nothing
        when the proof is flat (then output is just the entry);
      * ``"blocks"`` — the full nesting path, entry then each block outer→inner;
      * ``"entry"`` — no drill-down, the owning entry alone (original output).
    """
    for token in loci:
        parsed = _parse_locus(token)
        if parsed is None:
            print(f"{token}: expected FILE:LINE or FILE:A..B "
                  f"(e.g. Foo.thy:42 or Foo:8..12)", file=sys.stderr)
            continue
        file_token, lo, hi = parsed
        sec = _resolve_theory(sections, file_token)
        if sec is None:
            suggestion = _suggest_theory(sections, file_token)
            hint = f" (did you mean {suggestion}?)" if suggestion else ""
            print(f"{token}: no such theory '{file_token}'{hint}",
                  file=sys.stderr)
            continue
        # An open upper bound (`FILE:A..`) resolves to the theory's last line
        # here — the sink the range parser defers a `None` upper to.  The
        # `lo == hi` point-test stays on the *raw* hi (None never equals lo),
        # so `A..` is always a range, never mistaken for a single line.
        hi_eff = sec.thy_lines if hi is None else hi
        loc = (f"{sec.theory}:{lo}" if lo == hi
               else f"{sec.theory}:{lo}..{hi_eff}")
        if lo > sec.thy_lines:
            print(f"{loc} → (past end of {sec.theory} — "
                  f"{sec.thy_lines} lines)")
            continue
        if lo == hi:
            entry = _enclosing_entry(sec, lo)
            if entry is None:
                print(f"{loc} → (no enclosing entry — "
                      f"theory header or inter-section gap)")
                continue
            role = _locus_role(entry, lo)
            suffix = f"  ({role})" if role else ""
            base = (f"{loc} → {entry.name} ({entry.tag}) — {sec.theory} "
                    f"{_format_extent(entry)}")
            # Drill into the proof for the nearest/whole-path modes, but only
            # when the line is actually in a proof.  A flat (`by …`) proof or
            # an unbalanced scan yields no blocks, so output degrades to the
            # entry — exactly the `--entry` answer, with no `▸`.
            blocks: list[_Block] = []
            if block_mode != "entry" and role == "in proof":
                blocks = _enclosing_blocks(_proof_blocks(sec, entry) or [], lo)
            if not blocks:
                print(f"{base}{suffix}")
            elif block_mode == "blocks":
                print(f"{base}{suffix}")
                indent = " " * (len(loc) + len(" → "))
                width = max(len(_block_label(b)) for b in blocks)
                for b in blocks:
                    print(f"{indent}▸ {_block_label(b):<{width}} "
                          f"{b.start}..{b.end}")
            else:   # nearest: the innermost enclosing block
                print(f"{base} ▸ {_block_field(blocks[-1])}{suffix}")
            continue
        # Range: every entry whose [src_start, thy_end] overlaps [lo, hi_eff].
        overlap = sorted(
            (e for e in sec.entries if e.thy_line and e.thy_end
             and not (e.thy_end < lo or e.src_start > hi_eff)),
            key=lambda e: e.src_start)
        if not overlap:
            print(f"{loc} → (no entries overlap — "
                  f"theory header or inter-section gap)")
            continue
        for e in overlap:
            print(f"{loc} → {e.name} ({e.tag}) — {sec.theory} "
                  f"{_format_extent(e)}")


def cmd_callers(sections: list[TheorySection], name: str,
                flags: 'CmdFlags') -> None:
    """Print proof-body usages of a lemma/definition."""
    if flags.recursive:
        graph = _build_call_graph(sections, flags.drop_names_upto)
        if name not in graph.all_names:
            parent = _resolve_conjunct(sections, name)
            if parent is not None:
                print(f"# '{name}' is a named conjunct of {parent}; "
                      f"recursive caller closure operates at the {parent} "
                      f"(entry) level.")
                name = parent
            else:
                print(f"'{name}' not found in the entry index.")
                return
        reachable = _bfs_depths(lambda n: graph.callers.get(n, set()), {name})
        reachable.pop(name, None)
        _render_graph_results(sections, reachable, "caller", name, flags)
        return

    hits = _find_callers(sections, name, external=flags.external)
    if flags.mode == "count":
        print(len(hits))
        return
    if not hits:
        print(f"No callers found for '{name}'.")
        return
    # Build theory → section lookup once for enclosing-entry lookup and
    # trailing-context line access.
    by_theory = _sections_by_theory(sections)
    n_after = max(0, flags.context)
    # Align the match loci into a column; each is a clean `theory:line` that
    # pastes into `enclosing` / `lines` / an editor (no trailing marker).
    loc_w = max((len(f"{t}:{ln}") for t, ln, _ in hits), default=0)
    print(f"{len(hits)} caller(s) of {name}:\n")
    for theory, line_no, text in hits:
        sec = by_theory.get(theory)
        encl = _enclosing_entry(sec, line_no) if sec is not None else None
        loc = f"{theory}:{line_no}"
        print(f"  {loc:<{loc_w}}  {_owner_field(encl)}  {text.strip()}")
        if n_after > 0 and sec is not None:
            src = sec.source()
            # 1-indexed line_no → 0-indexed slice start at line_no
            # (i.e., the line *after* the match).  Context keeps ripgrep's
            # `-` marker — it flags the line as context, not a match, and
            # `_parse_locus` strips it so the locus still round-trips.
            for off, ctx in enumerate(src[line_no:line_no + n_after], start=1):
                ctx_no = line_no + off
                print(f"  {theory}:{ctx_no}-  {ctx.rstrip()}")


def cmd_callees(sections: list[TheorySection], name: str,
                flags: 'CmdFlags') -> None:
    """Entry-level forward edge: the entries this entry references in
    its proof body (its callees).  Pairs with `cmd_callers` (reverse).
    Not to be confused with the theory-level `deps` / `uses` pair."""
    graph = _build_call_graph(sections, flags.drop_names_upto)
    if name not in graph.all_names:
        parent = _resolve_conjunct(sections, name)
        if parent is not None:
            print(f"# '{name}' is a named conjunct of {parent}; "
                  f"reporting {parent}'s callees (shared proof body).")
            name = parent
        else:
            print(f"'{name}' not found in the entry index.")
            return

    if flags.recursive:
        reachable = _bfs_depths(lambda n: graph.callees.get(n, set()), {name})
        reachable.pop(name, None)
        _render_graph_results(sections, reachable, "dependency", name, flags)
        return

    by_name = _entry_by_name(sections)

    used = graph.callees.get(name, set())
    if flags.external:
        # Mirror of `callers --external`: drop callees defined in NAME's
        # own theory, leaving only its cross-theory dependencies.
        own_theory = by_name.get(name, (None,))[0]
        used = {u for u in used
                if by_name.get(u, (None,))[0] != own_theory}
    if flags.mode == "count":
        print(len(used))
        return
    if not used:
        scope = "cross-theory " if flags.external else ""
        print(f"No {scope}references found in {name}'s body.")
        return

    print(f"{len(used)} callee(s) of {name}:\n")
    for uname in sorted(used):
        if uname in by_name:
            thy, e = by_name[uname]
            print(f"  {uname} ({e.tag}) — {thy} [L{e.thy_line}]")
        else:
            print(f"  {uname}")


def cmd_methods(sections: list[TheorySection], name: str | None,
                flags: 'CmdFlags') -> None:
    """Proof-method usage, the complement of the citation graph.

    ``methods``         — ranked tally of every proof method used, with
                          occurrence counts and corpus share (``-a`` for the
                          full list, ``--names`` for names only, ``-c`` for the
                          distinct-method count).
    ``methods NAME``    — every live use of method NAME with its location and
                          owning entry (the method analogue of ``callers``).
    """
    counts, located = _scan_methods(sections, only=name)

    if name is None:
        if flags.mode == "count":
            print(len(counts))           # number of distinct methods used
            return
        if not counts:
            print("No proof-method uses found.")
            return
        ranked = counts.most_common()
        if flags.mode == "names":
            for meth, _c in ranked:
                print(meth)
            return
        total = sum(counts.values())
        shown = ranked if flags.mode == "all" else ranked[:30]
        suffix = "" if flags.mode == "all" else f" (top {len(shown)})"
        print(f"{len(counts)} proof methods used across {total} "
              f"by/apply/proof introducers{suffix}:\n")
        name_w = max(len(m) for m, _ in shown)
        for meth, c in shown:
            print(f"  {meth:<{name_w}}  {c:>8}  {100.0 * c / total:5.1f}%")
        if flags.mode != "all" and len(ranked) > len(shown):
            print(f"\n  ... {len(ranked) - len(shown)} more methods "
                  f"(use -a for all, or `methods NAME` for uses)")
        return

    # Located form: `methods NAME`.
    if name not in _isa_ns.PROOF_METHODS:
        print(f"'{name}' is not a known proof method "
              f"(method namespace: {_isa_ns.__name__}).  Try `methods` for "
              f"the list of methods actually used.")
        return
    if flags.mode == "count":
        print(len(located))
        return
    if not located:
        print(f"No uses of method '{name}' found.")
        return
    loc_w = max((len(f"{t}:{ln}") for t, ln, *_ in located), default=0)
    if flags.mode == "names":
        for theory, ln, owner, _text in located:
            print(f"  {f'{theory}:{ln}':<{loc_w}}  {_owner_field(owner)}")
        return
    print(f"{len(located)} use(s) of method '{name}':\n")
    for theory, ln, owner, text in located:
        loc = f"{theory}:{ln}"
        print(f"  {loc:<{loc_w}}  {_owner_field(owner)}  {text.strip()}")


def _compute_unused(graph: CallGraph,
                    keep: set[str] | None = None) -> set[str]:
    """Entries with zero callers (directly unused).

    Names in `keep` are treated as live roots — never flagged as unused
    regardless of caller count.  Use this to exclude top-of-pyramid
    theorems (e.g. AFP-headline statements) which legitimately have
    zero callers in the project but should not be pruned.
    """
    keep = keep or set()
    return {n for n in graph.all_names
            if n not in keep and not graph.callers.get(n, set())}


def _compute_unused_recursive(graph: CallGraph,
                              keep: set[str] | None = None
                              ) -> dict[str, int]:
    """Fixed-point cascade: an entry is unused if all its callers are unused.

    Names in `keep` are treated as live roots — never flagged, and
    entries whose callers include a kept name stay live too (the
    cascade stops at the live frontier).

    Returns {name: depth} where depth 0 = directly unused (zero callers),
    depth 1 = became unused when depth-0 entries are removed, etc.
    """
    keep = keep or set()
    unused: dict[str, int] = {n: 0 for n in _compute_unused(graph, keep)}
    changed = True
    depth = 1
    while changed:
        changed = False
        for name in graph.all_names - set(unused) - keep:
            callers = graph.callers.get(name, set())
            if callers and callers <= set(unused):
                unused[name] = depth
                changed = True
        depth += 1
    return unused


def _compute_forest(graph: CallGraph,
                    sections: list[TheorySection],
                    keep: set[str] | None = None
                    ) -> list[tuple[str, int, int, int, int]]:
    """Compute the forest of unused roots with exclusive subtree sizes.

    For each root (zero callers, modulo `keep`), compute:
    - total cone: all entries transitively reachable via callees
    - exclusive subtree: entries reachable ONLY from this root

    Names in `keep` are treated as live and excluded from the root
    set; their support cones don't contribute to the forest.

    Returns list of (root_name, exclusive_entries, exclusive_lines,
    total_entries, total_lines) sorted by exclusive_lines descending.
    """
    roots = _compute_unused(graph, keep)
    keep = keep or set()

    # For each entry, compute the set of roots that can reach it.
    # An entry is "exclusive" to a root iff its root-set is exactly
    # {root}.  Include kept (live) roots in the seed so that entries
    # shared between an unused root and a live root are NOT counted
    # as exclusive to the unused root — those would survive a prune.
    #
    # Fixed-point iteration:
    #   root_set(X) = {X}                            if X is a root
    #               = union(root_set(c) for c in callers(X))   else
    #
    # A single-pass BFS is INCORRECT here: a node's root-set must
    # accumulate from ALL its callers, but BFS-via-callees visits each
    # node once at first discovery, missing later-discovered caller
    # contributions.  The DAG (no cycles, per Isabelle theory order)
    # makes fixed-point iteration converge in O(longest-caller-chain)
    # passes.
    all_roots = roots | keep
    root_sets: dict[str, set[str]] = {r: {r} for r in all_roots}

    changed = True
    while changed:
        changed = False
        for name in graph.all_names:
            if name in all_roots:
                continue
            new_rset: set[str] = set()
            for c in graph.callers.get(name, set()):
                new_rset |= root_sets.get(c, set())
            if not new_rset:
                continue
            if root_sets.get(name) != new_rset:
                root_sets[name] = new_rset
                changed = True

    # Entry line-size lookup.
    entry_lines: dict[str, int] = {}
    for sec in sections:
        for e in sec.entries:
            if e.name in graph.all_names and e.name not in entry_lines:
                entry_lines[e.name] = e.line_count

    # For each root, compute exclusive entries (reachable only from it).
    # Total cone = all entries whose root-set includes this root.
    result: list[tuple[str, int, int, int, int]] = []
    for root in sorted(roots):
        exclusive_entries = 0
        exclusive_lines = 0
        total_entries = 0
        total_lines = 0
        for name, rset in root_sets.items():
            if root in rset:
                sz = entry_lines.get(name, 0)
                total_entries += 1
                total_lines += sz
                if len(rset) == 1:
                    exclusive_entries += 1
                    exclusive_lines += sz
        result.append((root, exclusive_entries, exclusive_lines,
                        total_entries, total_lines))

    result.sort(key=lambda x: -x[2])  # by exclusive lines desc
    return result


def _render_unused(entries: list[tuple[str, Entry, int]],
                   flags: 'CmdFlags', recursive: bool) -> None:
    """Shared rendering for unused and unused -r."""
    if not entries:
        print("No unused entries found.")
        return

    label = "transitively unused" if recursive else "unused"
    total = len(entries)

    if flags.mode == "count":
        print(total)
        return

    if flags.by_theory:
        theory_entries: dict[str, list[tuple[Entry, int]]] = {}
        for theory, e, depth in entries:
            theory_entries.setdefault(theory, []).append((e, depth))
        counts = Counter({t: len(es) for t, es in theory_entries.items()})
        total_lines = sum(
            e.line_count for es in theory_entries.values()
            for e, _ in es if e.thy_line > 0)
        print(f"{total} {label} entries across {len(theory_entries)} theories "
              f"({total_lines} source lines):\n")
        for theory, count in counts.most_common():
            tes = theory_entries[theory]
            lines = sum(e.line_count for e, _ in tes
                        if e.thy_line > 0)
            names = ", ".join(e.name for e, _ in tes[:4])
            if len(tes) > 4:
                names += f", ... (+{len(tes) - 4})"
            print(f"  {count:3d}  {theory:<30s}  {lines:5d} lines  {names}")
        return

    if recursive:
        direct = sum(1 for _, _, d in entries if d == 0)
        cascade = total - direct
        total_lines = sum(
            e.line_count for _, e, _ in entries
            if e.thy_line > 0)
        print(f"{total} {label} entries "
              f"({direct} direct + {cascade} cascading, "
              f"{total_lines} source lines):\n")
    else:
        print(f"{total} unused entries (zero callers):\n")

    print(f"{'Tag':<8}  {'Name':<42}  Theory  (span)")
    print(f"{'-' * 8:<8}  {'-' * 42:<42}  ------")
    for theory, e, depth in entries:
        size = e.line_count
        depth_mark = f"  [cascade depth {depth}]" if recursive and depth > 0 else ""
        print(f"{e.tag:<8}  {e.name:<42}  {theory}  "
              f"({e.src_start}..{e.thy_end}, {size} lines){depth_mark}")


def _render_forest(sections: list[TheorySection],
                   forest: list[tuple[str, int, int, int, int]],
                   flags: 'CmdFlags') -> None:
    """Render the forest root summary."""
    if not forest:
        print("No unused roots found.")
        return

    # Entry lookup for theory.
    by_name = _entry_by_name(sections)

    if flags.mode == "count":
        print(len(forest))
        return

    print(f"{len(forest)} unused roots:\n")
    print(f"  {'Root':<42s}  {'Excl':>5s}  {'Lines':>6s}  "
          f"{'Total':>5s}  {'Lines':>6s}  Theory")
    print(f"  {'-' * 42:<42s}  {'-' * 5:>5s}  {'-' * 6:>6s}  "
          f"{'-' * 5:>5s}  {'-' * 6:>6s}  ------")
    for root, ee, el, te, tl in forest:
        thy = by_name[root][0] if root in by_name else "?"
        print(f"  {root:<42s}  {ee:>5d}  {el:>6d}  {te:>5d}  {tl:>6d}  {thy}")


def cmd_unused(sections: list[TheorySection], flags: 'CmdFlags') -> None:
    """List entries with zero callers in proof bodies."""
    # `derived=True` here and nowhere else.  The call graph is over FACTS, and
    # `foo_def` is a different fact from `foo` — `test_substring_is_not_a_call`
    # pins exactly that, and `callers foo` keeps meaning `foo`.  Deadness,
    # though, is a question about the DECLARATION: deleting `definition foo`
    # breaks every proof citing `foo_def`, so such a proof keeps `foo` alive.
    # Asking the fact-level question here reports live definitions as dead.
    graph = _build_call_graph(sections, flags.drop_names_upto, derived=True)

    keep = set(flags.keep)
    if keep:
        unknown = keep - graph.all_names
        if unknown:
            print(f"warning: --keep names not found in call graph: "
                  f"{', '.join(sorted(unknown))}", file=sys.stderr)

    if flags.roots:
        forest = _compute_forest(graph, sections, keep)
        _render_forest(sections, forest, flags)
        return

    if flags.recursive:
        unused_map = _compute_unused_recursive(graph, keep)
    else:
        unused_map = {n: 0 for n in _compute_unused(graph, keep)}

    unused_entries: list[tuple[str, Entry, int]] = []
    for sec in sections:
        for e in sec.entries:
            if e.tag in _CITABLE_TAGS and e.name != "?":
                if e.name in unused_map:
                    unused_entries.append((sec.theory, e, unused_map[e.name]))

    _render_unused(unused_entries, flags, flags.recursive)


def _grep_sections(sections: list[TheorySection], pat: re.Pattern
                   ) -> list[tuple[str, int, str, "Entry | None", bool, bool]]:
    """Walk every section's source and return one tuple per line that
    matches `pat`.  Each tuple is (loc_name, line_no, line_text,
    owning_entry, is_live, is_thy), where loc_name is the file's real
    name (e.g. `Foo.thy`, `notes.md`) so plain non-`.thy`
    positionals report their actual filename rather than `<stem>.thy`.
    `is_thy` is False for non-`.thy` positionals (Markdown / prose),
    which have no Isabelle entries and hence no owning-entry column —
    `cmd_grep` shows the matched line text directly for those.

    is_live = True iff the line is genuine proof / declaration source —
    not inside a top-level `text \\<open>...\\<close>` block, not inside
    a per-entry preamble (a small text block attached to a following
    declaration), and not inside a multi-line `\\<comment>
    \\<open>...\\<close>` annotation.

    owning_entry is the lemma/theorem/definition whose span contains the
    matching line, via binary-search lookup (None if the line is outside
    any indexed entry — e.g. between top-level declarations).
    """
    line_index = _build_line_index(sections)
    out: list[tuple[str, int, str, Entry | None, bool, bool]] = []
    for sec in sections:
        lines = sec.source()
        noise = [range(lo, hi + 1) for lo, hi in _noise_spans(sec)]
        idx = line_index.get(sec.theory, [])
        # Resolve the line window once: no window → the whole file; an open
        # upper bound (`PATH:A..`) → this section's last line (the sink the
        # range parser defers a `None` upper to).  With no window the bounds
        # span the file, so the per-line test needs no separate None-guard.
        window = sec.line_window
        win_lo, win_hi = window if window is not None else (1, len(lines))
        if win_hi is None:
            win_hi = len(lines)
        for line_no_0, line in enumerate(lines):
            line_no = line_no_0 + 1
            if not (win_lo <= line_no <= win_hi):
                continue
            if not pat.search(line):
                continue
            is_live = not any(line_no in r for r in noise)
            owner = _entry_at_line(idx, line_no)
            out.append((sec.path.name, line_no, line.rstrip(), owner,
                        is_live, sec.is_thy))
    return out


def cmd_grep(sections: list[TheorySection], pattern: str,
             flags: 'CmdFlags') -> None:
    """Regex-search live source across all theories.

    Default: only matches in live source (declarations + proof bodies),
    skipping `text \\<open>...\\<close>` blocks, per-entry preambles, and
    multi-line `\\<comment> \\<open>...\\<close>` annotations.  Use
    `--with-comments` to also include prose matches; each non-live hit is
    tagged.

    Pattern accepts both Python regex syntax (`a|b|c`) and shell-grep-
    style alternation (`a\\|b\\|c`); the latter is rewritten to the
    former before compiling, mirroring `cmd_find`'s behaviour.
    """
    pattern = pattern.replace(r"\|", "|")
    try:
        pat = re.compile(pattern)
    except re.error as exc:
        print(f"ERROR: invalid regex '{pattern}': {exc}", file=sys.stderr)
        sys.exit(2)

    all_hits = _grep_sections(sections, pat)
    live_hits = [h for h in all_hits if h[4]]
    dead_hits = [h for h in all_hits if not h[4]]
    hits = all_hits if flags.with_comments else live_hits

    if flags.mode == "count":
        print(len(all_hits) if flags.with_comments else len(live_hits))
        return

    if not hits:
        print(f"No {'' if flags.with_comments else 'live '}"
              f"matches for '{pattern}'.")
        return

    if flags.with_comments:
        print(f"{len(all_hits)} match(es) for '{pattern}' "
              f"({len(live_hits)} live, "
              f"{len(dead_hits)} in comments/text):\n")
    else:
        print(f"{len(live_hits)} live match(es) for '{pattern}':\n")

    if flags.mode == "names":
        # Compact: location + owning entry, no source line.  For a
        # non-`.thy` positional there is no owning entry, so names mode
        # would be content-free — fall back to the matched line text.
        loc_w = max((len(f"{t}:{ln}") for t, ln, *_ in hits), default=0)
        for loc_name, ln, text, owner, is_live, is_thy in hits:
            loc = f"{loc_name}:{ln}"
            marker = "" if is_live else "  [in comment/text]"
            if not is_thy:
                print(f"  {loc:<{loc_w}}  {text.strip()}{marker}")
                continue
            print(f"  {loc:<{loc_w}}  {_owner_field(owner, span=False)}{marker}")
        return

    # Default: location + owning entry + matched line text.  Non-`.thy`
    # positionals have no entry column — show the line inline on one row.
    loc_w = max((len(f"{t}:{ln}") for t, ln, *_ in hits), default=0)
    for loc_name, ln, text, owner, is_live, is_thy in hits:
        loc = f"{loc_name}:{ln}"
        marker = "" if is_live else "  [in comment/text]"
        if not is_thy:
            print(f"  {loc:<{loc_w}}  {text.strip()}{marker}")
            continue
        print(f"  {loc:<{loc_w}}  {_owner_field(owner, span=False)}{marker}")
        print(f"    {text.strip()}")


def cmd_sorry(sections: list[TheorySection], count_only: bool) -> None:
    r"""List open goals: every live `sorry` as its location + owning entry.

    A thin specialisation of `grep` over the fixed `sorry` token, sharing
    the same `_grep_sections` engine.  Two refinements over a bare
    `grep '\bsorry\b'`: the boundary is prime-aware (`_isa_word_pattern`,
    so the identifier `sorry'` is not a false hit, unlike Python's `\b`),
    and only *live* matches count (a `sorry` inside a `text` / `\<comment>`
    block is not an open goal).  Replaces both the count-only
    `grep -c '\bsorry\b'` idiom and the shell sorry-counter formerly in
    `count-axioms.sh`.  `-c` prints the bare count (build-summary form);
    otherwise prints `FILE:LINE  entry (TAG)` per goal then a total.
    """
    pat = re.compile(_isa_word_pattern("sorry"))
    hits = [h for h in _grep_sections(sections, pat) if h[4]]
    if count_only:
        print(len(hits))
        return
    if not hits:
        print("No sorries.")
        return
    loc_w = max(len(f"{loc}:{ln}") for loc, ln, *_ in hits)
    for loc_name, ln, _text, owner, _live, _is_thy in hits:
        print(f"  {f'{loc_name}:{ln}':<{loc_w}}  {_owner_field(owner, span=False)}")
    print(f"{len(hits)} sorr{'y' if len(hits) == 1 else 'ies'}")


def _parse_line_range(spec: str) -> tuple[int, int | None]:
    """Parse `A..B`, `A..` (to EOF), `..B` (from line 1), or `A` into an
    inclusive (start, end) pair.  Raises ValueError on malformed input.

    An *open upper* bound (`A..`) comes back as ``end is None``: this parser
    holds no file, so "to EOF" can only be resolved by the caller that knows
    the source length.  An open *lower* bound (`..B`) needs no sentinel —
    the start of a file is always line 1 — so it resolves right here.  Every
    range surface (`lines`, the `enclosing`/grep `FILE:A..B` locus) funnels
    through this one split, so the open forms light up everywhere at once;
    each sink substitutes its own length for a `None` upper bound.
    """
    if ".." in spec:
        a_str, b_str = spec.split("..", 1)
        a = 1 if a_str == "" else int(a_str)
        b = None if b_str == "" else int(b_str)
    else:
        a = b = int(spec)
    if a < 1 or (b is not None and b < a):
        raise ValueError(f"invalid range '{spec}': require 1 <= start <= end")
    return a, b


# The PATH sentinel `-` means "read from standard input".  A piped stream
# has no on-disk path, so stdin content is carried on this synthetic one;
# its `.name` (`<stdin>`) is what `grep`/`sorry` print as the location.
_STDIN_SENTINEL = "-"
_STDIN_NAME = "<stdin>"
_STDIN_PATH = Path(_STDIN_NAME)


def _read_stdin_lines() -> list[str]:
    """Read **all** of standard input as a list of lines (the `-` sentinel).

    The whole stream is consumed up front and then numbered from 1, so a
    caller's `A..B` ranges line up with the piped content's own numbering:
    `git show REF:FILE | query lines - A..B` sees exactly the line numbers
    `FILE` had at `REF`.  (The anchor is lost only if the *producer* slices
    before piping — reading the whole stream here never does.)
    """
    return sys.stdin.read().splitlines()


def cmd_lines(source_lines: list[str], ranges: list[str]) -> None:
    """Print the given RANGEs of `source_lines` with `NR| CONTENT` prefix.

    Sandbox-friendly alternative to `awk 'NR>=A && NR<=B {…}'` loops;
    multiple ranges separated by blank lines (rg-style `--` separators
    between hunks).  Width of the line-number column adapts to the
    largest line number requested.

    `lines` is *ignore-syntax* (raw text, no theory parsing), so it takes
    already-read content rather than a path: token routing — path, the `-`
    stdin sentinel, or a bare theory name — is the caller's job, done once
    through the shared `_resolve_file_source` (see `_run_lines`).  Because
    the whole source is handed over un-sliced, the printed `NR` matches the
    source's own 1-based numbering.
    """
    try:
        parsed = [_parse_line_range(r) for r in ranges]
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        sys.exit(2)
    n_lines = len(source_lines)
    # Resolve an open upper bound (`A..`) to the last line now that the length
    # is known — this is the sink the parser defers a `None` upper to.  Carry
    # the open-ness so a diagnostic echoes the spec the user typed (`A..`,
    # not `A..<n_lines>`).
    resolved = [(a, n_lines if b is None else b, b is None) for a, b in parsed]
    max_no = max((b for _, b, _ in resolved), default=1)
    width = len(str(min(max_no, n_lines)))
    for i, (a, b, open_end) in enumerate(resolved):
        if i > 0:
            print("--")
        disp = f"{a}.." if open_end else f"{a}..{b}"
        a_clamped = max(1, a)
        b_clamped = min(n_lines, b)
        if a_clamped > n_lines:
            print(f"# range {disp}: past end of file ({n_lines} lines)",
                  file=sys.stderr)
            continue
        for nr in range(a_clamped, b_clamped + 1):
            print(f"{nr:>{width}}| {source_lines[nr - 1]}")
        if b > n_lines:
            print(f"# range {disp}: truncated at line {n_lines}",
                  file=sys.stderr)


def cmd_largest(sections: list[TheorySection], top: int = 20) -> None:
    # Theory/file scoping is handled upstream by `_load_sections` (the `files`
    # positionals); here we just rank whatever sections we were handed.
    rows: list[tuple[int, Entry, TheorySection]] = []
    for s in sections:
        for e in s.entries:
            if e.thy_line > 0:
                rows.append((e.line_count, e, s))

    rows.sort(key=lambda x: -x[0])

    if not rows:
        print("No entries found.")
        return

    print(f"Top {min(top, len(rows))} largest entries:\n")
    print(f"{'Lines':>6}  {'Tag':<8}  {'Name':<42}  Theory  (span)")
    print(f"{'-' * 6:>6}  {'-' * 8:<8}  {'-' * 42:<42}  ------")
    for size, e, s in rows[:top]:
        print(f"{size:>6}  {e.tag:<8}  {e.name:<42}  {s.theory}  ({e.src_start}..{e.thy_end})")


# ---------------------------------------------------------------------------
# Argument parsing (argparse with subcommands)
# ---------------------------------------------------------------------------

import argparse


@dataclass
class CmdFlags:
    """Uniform flag bundle passed to command functions."""
    mode: str = "first"          # first / all / count / names
    verbatim: bool = False       # -V / --verbatim
    statement: bool = False      # --statement / --stmt
                                 # find: match the statement slice (input);
                                 # show: render only the statement slice (output)
    comments: str = "on"         # on / off / only
    context: int = 2             # -U N / --context N
    with_comments: bool = False  # --with-comments (find + grep: search prose)
    recursive: bool = False      # -r / --recursive
    by_theory: bool = False      # --by-theory (unused)
    roots: bool = False          # --roots (unused)
    keep: frozenset[str] = frozenset()  # --keep (unused: live roots)
    external: bool = False       # --external (callers: skip defining theory)
    drop_names_upto: int = _DROP_NAMES_UPTO  # --drop-names-upto (call graph)


def _flags_from_ns(ns: argparse.Namespace) -> CmdFlags:
    """Build CmdFlags from an argparse Namespace."""
    f = CmdFlags()
    # Precedence: count > names > all > default ("first").
    if getattr(ns, "all", False):
        f.mode = "all"
    if getattr(ns, "names", False):
        f.mode = "names"
    if getattr(ns, "count", False):
        f.mode = "count"
    f.verbatim = getattr(ns, "verbatim", False)
    f.statement = getattr(ns, "statement", False)
    if getattr(ns, "no_comments", False):
        f.comments = "off"
    elif getattr(ns, "comments_only", False):
        f.comments = "only"
    f.context = getattr(ns, "context", 2)
    f.with_comments = getattr(ns, "with_comments", False)
    f.recursive = getattr(ns, "recursive", False)
    f.by_theory = getattr(ns, "by_theory", False)
    f.roots = getattr(ns, "roots", False)
    keep_args = getattr(ns, "keep", None) or []
    f.keep = frozenset(n for arg in keep_args
                       for n in arg.split(",") if n.strip())
    f.external = getattr(ns, "external", False)
    f.drop_names_upto = getattr(ns, "drop_names_upto", _DROP_NAMES_UPTO)
    return f


# -- FILES routing (shared by every `query CMD FILES`-shaped command) --------
#
# Routing answers *where the bytes are*; the command's parse policy answers
# *whether to read them as Isabelle*.  Keeping them separate is why one token
# resolver serves both `lines` (ignore-syntax, raw text) and the search family
# (`largest`/`sorry` syntax-aware, `grep` inferred) without either reinventing
# `-`/path/name resolution.

@dataclass
class FileSource:
    """A resolved `CMD FILES` token, decoupled from how a command reads it.

    `label` is the display/theory name, `path` the real or synthetic
    (`<stdin>`) path.  `preread` carries content that has no path to re-read
    (stdin); on-disk sources leave it ``None`` and are read lazily, so the
    AFP-scale memory profile is unchanged (nothing is materialised until a
    command actually parses or slices it).
    """
    label: str
    path: Path
    preread: list[str] | None = None

    @property
    def from_stdin(self) -> bool:
        return self.path == _STDIN_PATH

    def lines(self) -> list[str]:
        """The source's raw lines — the pre-read content, or the file read
        on demand."""
        if self.preread is not None:
            return self.preread
        return self.path.read_text().splitlines()


def _stdin_source() -> FileSource:
    """The one-shot `-` source: standard input read once, in full."""
    return FileSource(_STDIN_NAME, _STDIN_PATH, _read_stdin_lines())


def _resolve_file_source(token: str, p: Path,
                         get_index) -> FileSource:
    """Resolve one non-`-`, non-directory FILES token to a `FileSource`.

    `p` is the caller's already-resolved ``Path(token)``.  An existing file
    resolves to itself; otherwise the token is treated as a bare theory
    **name** (or a path whose stem names one), looked up in the lazily-built
    index via `get_index` — matching how outline/show/defs/callees take
    names.  A token that is neither exits with a 'did you mean ...?' hint.

    This is the single home of path/name routing: `_load_sections` and
    `_run_lines` both call it, so the two can never drift on what a token
    means.
    """
    if p.exists():
        return FileSource(p.stem, p)
    index = get_index()
    sec = _resolve_theory(index, token)
    if sec is not None:
        return FileSource(sec.path.stem, sec.path)
    suggestion = _suggest_theory(index, token)
    hint = f" (did you mean {suggestion}?)" if suggestion else ""
    print(f"ERROR: not a path or known theory: {token}{hint}",
          file=sys.stderr)
    sys.exit(1)


def _section_from(src: FileSource, parse: str) -> TheorySection:
    """Parse a source into a TheorySection under the command's parse policy.

    `parse="syntax"` always applies the Isabelle entry grammar — for
    `largest`/`sorry`, whose output *is* the entry view, syntax-awareness is
    intrinsic, not a property of the file.  `parse="infer"` (only `grep`, the
    command where it is genuinely unclear) decides per source from the one
    piece of evidence available: the `.thy` suffix, with stdin — which has no
    suffix — defaulting to syntax-aware (the load-bearing case is a piped
    theory).  The suffix is thus *evidence for the ambiguous case*, never the
    primary switch.
    """
    syntactic = parse == "syntax" or src.from_stdin or src.path.suffix == ".thy"
    if syntactic:
        return _parse_one(src.label, src.path, src.preread)
    return _parse_plain(src.label, src.path, src.preread)


def _split_path_window(token: str, get_index
                       ) -> tuple[tuple[int, int | None] | None, str]:
    """Peel an optional `:A..B` / `:LINE` window off a grep PATH positional.

    Returns ``(window, file_token)``.  The suffix is treated as a window
    *only* when the part before it resolves to an existing file or a known
    theory — otherwise the token is returned unchanged, so a path that
    happens to end in a colon, the `-` stdin sentinel, or a plain bad token
    all fall through to the normal resolver and its existing error.  Reuses
    `_parse_locus`, so the window grammar (`A..B`, trailing-marker tolerance)
    matches `enclosing`.
    """
    locus = _parse_locus(token)
    if locus is None:
        return None, token
    file_token, lo, hi = locus
    resolves = (Path(file_token).expanduser().exists()
                or _resolve_theory(get_index(), file_token) is not None)
    return ((lo, hi), file_token) if resolves else (None, token)


def _load_sections(ns: argparse.Namespace, parse: str = "infer", *,
                   windows: bool = False) -> list[TheorySection]:
    """Load theory sections from trailing positional PATHs, or the
    project ROOTs.

    Subcommands in the *search* family that accept ``nargs='*'`` trailing
    path positionals (``grep PATTERN ...``, ``largest ...``, ``sorry ...``)
    pre-populate ``ns.files``; the parse is then restricted to those paths
    instead of the full project index.  The *lookup* family
    (``callers``/``callees``/``show``/...) carries no PATH positionals —
    ``getattr(ns, "files", None)`` is falsy there, so they load the full
    index and scope via the global ``-R/--root``.

    Each positional may be:

    * ``-``  -> read one theory from **standard input** (the stdin
      sentinel), so the whole search family operates on piped content that
      never hit disk — ``git show REF:FILE | query grep PAT -``.
    * a ``.thy`` file path  -> that single theory.
    * a directory containing a ``ROOT`` file  -> all theories
      declared by ROOT (resolved through ROOT's ``theories`` and
      ``directories`` clauses, matching Isabelle's own semantics).
    * a directory with no ``ROOT``  -> recursive ``*.thy`` glob.

    When ``windows`` is set (grep only), a positional may carry a trailing
    ``:A..B`` (or ``:LINE``) line window — ``Foo.thy:100..200`` — scoping the
    search to those lines.  The file part resolves as usual and the window is
    attached to the section for `_grep_sections` to honour.

    Results are unioned and deduplicated by resolved absolute
    path, so passing two directories where one holds symlinks into
    the other does not double-count the shared theories.

    `parse` is the caller's parse policy, applied to single-file and stdin
    sources (a directory always yields syntax-aware `.thy` sections):
    ``"syntax"`` forces the entry grammar (`largest`/`sorry`), ``"infer"``
    decides per source from the `.thy` suffix (`grep`).  See `_section_from`.
    Token routing itself is delegated to `_resolve_file_source`, shared with
    `lines`.
    """
    files: list[str] = list(getattr(ns, "files", None) or [])
    if not files:
        return load_index()
    sections: list[TheorySection] = []
    seen_paths: set[Path] = set()
    index_cache: list[list[TheorySection]] = []  # memo box for name lookups

    def get_index() -> list[TheorySection]:
        if not index_cache:
            index_cache.append(load_index())
        return index_cache[0]

    stdin_read = False
    for token in files:
        if token == _STDIN_SENTINEL:
            # stdin is one-shot: a repeated `-` would read an exhausted
            # stream, so consume it at most once.
            if not stdin_read:
                stdin_read = True
                sections.append(_section_from(_stdin_source(), parse))
            continue
        window: tuple[int, int] | None = None
        if windows:
            window, token = _split_path_window(token, get_index)
        p = Path(token).expanduser().resolve()
        if p.is_dir():
            _sections_from_dir(p, seen_paths, sections)
            continue
        src = _resolve_file_source(token, p, get_index)
        resolved = src.path.resolve()
        if resolved in seen_paths:
            continue
        seen_paths.add(resolved)
        sec = _section_from(src, parse)
        sec.line_window = window
        sections.append(sec)
    return sections


# -- Shared flag groups (added to subparsers that need them) ----------------

def _add_mode_flags(p: argparse.ArgumentParser) -> None:
    # Composite bundle for subparsers that accept all three.  Not mutually
    # exclusive: -a --names composes (= "all matches as names").  Precedence
    # at resolution: -c > --names > -a > default.  Subparsers wanting only a
    # subset call the per-flag helpers (`_add_count_flag`,
    # `_add_names_flag`) directly.
    p.add_argument("-a", "--all", action="store_true",
                   help="show all matches")
    _add_count_flag(p, "just print the count (wins over -a / --names)")
    _add_names_flag(p, "names + tags + theory only (composable with -a)")


def _add_count_flag(p: argparse.ArgumentParser,
                    help_text: str = "just print the count") -> None:
    p.add_argument("-c", "--count", action="store_true", help=help_text)


def _add_names_flag(p: argparse.ArgumentParser,
                    help_text: str = "names + tags + theory only") -> None:
    # No `-n` short flag: it collides with the universal grep/rg convention
    # where `-n` = line numbers.  This tool always prints `theory:line`
    # locations, so there is nothing for a grep-style `-n` to toggle; rather
    # than squat on it for `--names` (a silent, surprising mode switch for
    # anyone with grep muscle memory), we leave `-n` free for its
    # conventional meaning and spell the terse view out as `--names`.
    p.add_argument("--names", action="store_true", help=help_text)


def _add_with_comments_flag(
        p: argparse.ArgumentParser,
        help_text: str = "also search inside `text` blocks and "
                         "\\<comment> annotations (default: live source "
                         "only)") -> None:
    # The search family's single "widen into cartouche prose" toggle, spelled
    # the same on `find` and `grep`.  No `-a` short flag: on `find`, `-a`
    # already means "show all matches" (the lookup-family mode from
    # `_add_mode_flags`), so giving `grep` `-a` for prose would fork `-a`'s
    # meaning across the two search verbs — the same trap as the dropped `-n`.
    # One concept, one word: `--with-comments`.
    p.add_argument("--with-comments", action="store_true", help=help_text)


def _add_path_files_arg(p: argparse.ArgumentParser) -> None:
    """Add the rg/grep-style trailing PATH positionals.

    Resolved by `_load_sections`: each may be a .thy file (single
    theory), a directory containing a ROOT (theories per ROOT's
    `theories` clause), or a directory without (recursive *.thy glob).
    Results dedup'd by resolved path so `t/ archive/` doesn't double-
    count symlinked theories.
    """
    p.add_argument("files", nargs="*", metavar="PATH",
                   help="restrict search to specific .thy files or "
                        "directories (rg/grep-style trailing positionals); "
                        "a bare theory name resolves to its .thy, and `-` "
                        "reads a theory from stdin (e.g. `git show REF:FILE "
                        "| query grep PAT -`). "
                        "Directories with a ROOT are expanded via the "
                        "ROOT's `theories` clause; directories without are "
                        "walked recursively for `*.thy`.  Results are "
                        "dedup'd by resolved path, so `t/ archive/` does "
                        "not double-count symlinked theories.")


def _add_subject_list_arg(p: argparse.ArgumentParser, *, cmd: str,
                          dest: str = "name", metavar: str = "NAME",
                          noun: str = "entry name",
                          verb: str = "report each",
                          extra: str = "") -> None:
    """Shared one-or-more positional for every command that takes a list of
    subjects and processes them in turn — the lookup family
    (`show`/`callers`/`callees`, `deps`/`uses`) plus `find`.

    The list form is the load-bearing reason to prefer `query` over a shell
    loop: `query CMD A B C` does in one gate-free call what
    `for n in A B C; do query CMD $n` does in N gate-tripping ones.  Routing
    them all through this template keeps the shared part of their `--help`
    byte-identical (only `extra` carries the command-specific addendum), so
    the wording can't drift command-to-command.  The search family's *scope*
    positional is the separate `_add_path_files_arg`; subjects and paths
    never share a slot, which is what keeps the two families distinct.
    """
    help_text = (f"{noun}(s); pass multiple to {verb} in turn "
                 f"(blank-line separated), so `{cmd} A B C` replaces a "
                 f"gate-tripping `for n in A B C; do {cmd} $n` loop")
    if extra:
        help_text = f"{help_text}.  {extra}"
    p.add_argument(dest, nargs="+", metavar=metavar, help=help_text)


def _add_verbatim_flag(p: argparse.ArgumentParser) -> None:
    # `p` may be a parser or a mutually-exclusive group (both expose
    # add_argument), so `show` can pair this with `--statement` in one group.
    p.add_argument("-V", "--verbatim", action="store_true",
                   help="full source slice (statement + proof)")

def _add_statement_flag(p: argparse.ArgumentParser, *, help_text: str) -> None:
    # The statement slice (the declaration, not the proof) as a locus.  The
    # *meaning* differs by verb — `find` matches it, `show` renders it — so
    # the help text is per-verb, but the spelling (`--statement`, alias
    # `--stmt`, dest `statement`) is shared so it can't drift.
    p.add_argument("--statement", "--stmt", dest="statement",
                   action="store_true", help=help_text)

def _add_comment_flags(p: argparse.ArgumentParser) -> None:
    g = p.add_mutually_exclusive_group()
    g.add_argument("--no-comments", action="store_true",
                   help="suppress preamble and roadmap")
    g.add_argument("--comments-only", action="store_true",
                   help="show only preamble + roadmap")

def _add_context_flag(p: argparse.ArgumentParser, *, default: int = 2,
                      help_text: str = "") -> None:
    # One short flag for `--context` across every command that has it: `-U`
    # (the established spelling on the lookup family — theory/outline/find/
    # show).  `callers` routes through here too rather than declaring its own
    # `-C` inline: it is a lookup-family verb (it carries no PATH positionals),
    # so it should match its family, and rg's `-C` means context on *both*
    # sides whereas callers shows only trailing lines (rg's `-A`) — so `-C`
    # was a mis-aligned borrowing anyway.  Only the default differs per
    # command (preview wants 2, a caller listing wants 0), so it is a param.
    help_text = help_text or f"lines of preview / context (default {default})"
    p.add_argument("-U", "--context", type=int, default=default, metavar="N",
                   help=help_text)

def _add_drop_names_flag(p: argparse.ArgumentParser) -> None:
    # Filter short citation names out of the call graph: a length-1 token
    # (`x`, `a`, `f`) is a term variable in nearly every proof, so by default
    # (L=1) single-char names are not graph nodes.  L=0 keeps them; L=2 also
    # drops 2-char names.  Method/keyword/numeral routing is independent.
    p.add_argument("--drop-names-upto", type=int, default=_DROP_NAMES_UPTO,
                   metavar="L",
                   help=f"exclude citation-graph names of length <= L "
                        f"(default {_DROP_NAMES_UPTO}: drop single-char "
                        f"variable collisions; 0 keeps all; 2 also drops "
                        f"2-char names)")


# -- Subcommand handlers (thin wrappers) -----------------------------------

def _run_each(ns: argparse.Namespace, attr: str, fn) -> None:
    """Load sections once, then apply ``fn(sections, subject)`` to each subject
    in ``getattr(ns, attr)``, blank-line-separated — the shared spine of the
    list-taking subcommands (``deps``/``uses``/``find``/``show``/``callers``/
    ``callees``), so ``CMD A B C`` does in one gate-free call what a shell
    ``for`` loop does in N.
    """
    sections = _load_sections(ns)
    for i, subject in enumerate(getattr(ns, attr)):
        if i > 0:
            print()
        fn(sections, subject)


def _run_summary(ns: argparse.Namespace) -> None:
    cmd_summary(_load_sections(ns))

def _run_theory(ns: argparse.Namespace) -> None:
    cmd_theory(_load_sections(ns), ns.name, _flags_from_ns(ns))

def _run_defs(ns: argparse.Namespace) -> None:
    cmd_defs(_load_sections(ns), ns.theory, _flags_from_ns(ns))

def _run_deps(ns: argparse.Namespace) -> None:
    _run_each(ns, "theory",
              lambda secs, thy: cmd_deps(secs, thy, recursive=ns.recursive))

def _run_theory_uses(ns: argparse.Namespace) -> None:
    _run_each(ns, "theory", lambda secs, thy:
              cmd_deps(secs, thy, reverse=True, recursive=ns.recursive))

def _run_outline(ns: argparse.Namespace) -> None:
    cmd_outline(_load_sections(ns), ns.theory, _flags_from_ns(ns))

def _run_enclosing(ns: argparse.Namespace) -> None:
    # No PATH positionals: the FILE is baked into each FILE:LINE locus, so
    # load the full `-R`-scoped index and resolve each file token against it.
    mode = ("entry" if ns.entry else "blocks" if ns.blocks else "nearest")
    cmd_enclosing(_load_sections(ns), ns.locus, mode)

def _run_largest(ns: argparse.Namespace) -> None:
    # largest ranks *entries* by span — syntax-awareness is intrinsic.
    cmd_largest(_load_sections(ns, parse="syntax"), ns.top)

def _run_find(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "pattern", lambda secs, pat: cmd_find(secs, pat, flags))

def _run_show(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_show(secs, n, flags))

def _run_callers(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_callers(secs, n, flags))

def _run_callees(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_callees(secs, n, flags))

def _run_unused(ns: argparse.Namespace) -> None:
    cmd_unused(_load_sections(ns), _flags_from_ns(ns))

def _run_methods(ns: argparse.Namespace) -> None:
    cmd_methods(_load_sections(ns), ns.name, _flags_from_ns(ns))

def _run_grep(ns: argparse.Namespace) -> None:
    # grep is the one command where the parse mode is genuinely unclear
    # (live source vs. plain prose), so it infers per source.  It is also the
    # only search verb that honours a `PATH:A..B` line window (windows=True),
    # to scope a search to a hunk of a file that matches hundreds of times.
    cmd_grep(_load_sections(ns, parse="infer", windows=True), ns.pattern,
             _flags_from_ns(ns))

def _run_sorry(ns: argparse.Namespace) -> None:
    # sorry lists open goals in proofs — a theory concept; always syntax-aware.
    cmd_sorry(_load_sections(ns, parse="syntax"), getattr(ns, "count", False))

def _lines_file_and_ranges(tokens: list[str]) -> tuple[str, list[str]]:
    """Split `lines` positionals into ``(file_token, ranges)``.

    Two accepted spellings, detected by whether the first token parses as a
    ``FILE:RANGE`` locus:

      * ``FILE RANGE...``        — ``lines Foo 1..10 20..30``  (the original)
      * ``FILE:RANGE ...``       — ``lines Foo:1..10 Foo:20..30``

    The colon form is the `enclosing` / grep locus grammar reused, so a span
    printed elsewhere pastes straight in; its loci must name **one** file
    (`cmd_lines` reads a single source).  Exits with a clear error on a
    mixed or multi-file colon batch, or a bare ``FILE`` with no ranges.
    """
    if _parse_locus(tokens[0]) is not None:
        loci = []
        for t in tokens:
            parsed = _parse_locus(t)
            if parsed is None:
                print(f"ERROR: mixed `lines` forms — '{t}' is not FILE:RANGE",
                      file=sys.stderr)
                sys.exit(2)
            loci.append(parsed)
        files = {f for f, _, _ in loci}
        if len(files) > 1:
            print(f"ERROR: `lines` reads one file, got: "
                  f"{', '.join(sorted(files))}", file=sys.stderr)
            sys.exit(2)
        return loci[0][0], [
            (f"{lo}.." if hi is None else f"{lo}..{hi}") for _, lo, hi in loci]
    if len(tokens) < 2:
        print("ERROR: `lines` needs at least one RANGE "
              "(`FILE RANGE...` or `FILE:RANGE ...`)", file=sys.stderr)
        sys.exit(2)
    return tokens[0], tokens[1:]


def _run_lines(ns: argparse.Namespace) -> None:
    # lines is ignore-syntax: route the file token to its source through the
    # shared resolver (same `-`/path/name handling as the search family), then
    # hand the raw lines to cmd_lines.  `_lines_file_and_ranges` accepts both
    # the `FILE RANGE...` and colon-form `FILE:RANGE ...` spellings.
    file_token, ranges = _lines_file_and_ranges(ns.args)
    if file_token == _STDIN_SENTINEL:
        src = _stdin_source()
    else:
        src = _resolve_file_source(file_token,
                                   Path(file_token).expanduser().resolve(),
                                   load_index)
    cmd_lines(src.lines(), ranges)


# -- Parser construction ----------------------------------------------------

def _resolve_version() -> str:
    """The installed distribution version, read from package metadata.

    Single source of truth: the version lives only in `pyproject.toml` and is
    baked into the installed dist metadata at build/install time; we read it
    back here rather than duplicating a `__version__` literal that the release
    bump (and `make release`'s tomllib read) would then have to keep in sync.
    Caveat for editable installs: the metadata version reflects the last
    `pip install -e`, so it can lag the working tree even though the running
    code is live — the label is the installed version, not the checkout's.
    """
    from importlib.metadata import PackageNotFoundError, version
    try:
        return version("isabelle-query")
    except PackageNotFoundError:
        return "0+unknown (package not installed)"


class _VersionAction(argparse.Action):
    """Lazy `--version`.

    argparse's built-in `action="version"` wants a precomputed string, which
    would force the `importlib.metadata` import + dist-info scan on *every*
    `query` run.  Deferring it to `__call__` means only an actual
    `query --version` pays that cost — keeping the common path sub-100ms.
    """
    def __init__(self, option_strings, dest=argparse.SUPPRESS,
                 default=argparse.SUPPRESS,
                 help="show the version and exit"):
        super().__init__(option_strings=option_strings, dest=dest,
                         default=default, nargs=0, help=help)

    def __call__(self, parser, namespace, values, option_string=None):
        print(f"query {_resolve_version()}")
        parser.exit()


def _build_parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser(
        prog="query",
        description="Query the theory index — computed live from .thy files.",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    top.add_argument(
        "-R", "--root", metavar="DIR",
        help="Isabelle session directory to query — the directory "
             "containing ROOT, or a parent of per-session ROOTs.  "
             "Overrides $ISABELLE_QUERY_ROOT, any .isabelle-query marker, and "
             "auto-discovery.  Must precede the subcommand.")
    top.add_argument("--version", action=_VersionAction)

    sub = top.add_subparsers(dest="command", title="commands")

    # summary
    p = sub.add_parser("summary", help="theory overview table")
    p.set_defaults(func=_run_summary)

    # theory
    p = sub.add_parser("theory",
                       help="show all entries for a theory "
                            "(--names for a terse namespace listing)")
    p.add_argument("name", help="theory name")
    _add_names_flag(p, "list the theory's namespace entries terse "
                       "(name, tag, line; no bodies) — one per line")
    _add_count_flag(p, "just print the entry count")
    _add_verbatim_flag(p)
    _add_comment_flags(p)
    _add_context_flag(p)
    p.set_defaults(func=_run_theory)

    # defs
    p = sub.add_parser("defs",
                       help="list definitions in a theory "
                            "(--names for terse name listing)")
    p.add_argument("theory", help="theory name")
    _add_names_flag(p, "list definition names terse (name, tag, line)")
    _add_count_flag(p, "just print the definition count")
    p.set_defaults(func=_run_defs)

    # deps
    p = sub.add_parser("deps",
                       help="theories these import (direct; -r for "
                            "transitive); reverse is `uses`")
    _add_subject_list_arg(p, cmd="deps", dest="theory", metavar="THEORY",
                          noun="theory name or .thy path")
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect imports)")
    p.set_defaults(func=_run_deps)

    # uses (theory-level reverse of deps; brew's deps/uses convention)
    p = sub.add_parser("uses",
                       help="theories that import these (direct; -r for "
                            "transitive); reverse of `deps`")
    _add_subject_list_arg(p, cmd="uses", dest="theory", metavar="THEORY",
                          noun="theory name or .thy path")
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect importers)")
    p.set_defaults(func=_run_theory_uses)

    # outline
    p = sub.add_parser("outline", help="section structure with entries")
    p.add_argument("theory", help="theory name")
    _add_comment_flags(p)
    _add_context_flag(p)
    p.set_defaults(func=_run_outline)

    # enclosing (alias: at) — the inverse of outline: name the entry that
    # owns a FILE:LINE locus, for the build-chase loop "which lemma is at
    # line N".  Lookup-family (no PATH positionals; the FILE is in the locus).
    p = sub.add_parser("enclosing", aliases=["at"],
                       help="name the entry (and nearest proof block) that "
                            "owns each FILE:LINE locus (or every entry a "
                            "FILE:A..B range touches; inverse of outline, "
                            "for build-failure triage)")
    p.add_argument("locus", nargs="+", metavar="FILE:LINE",
                   help="one or more loci, each `FILE:LINE` (e.g. Foo.thy:42 "
                        "or, by bare theory name, Foo:42) or `FILE:A..B` for "
                        "a line range (e.g. Foo:8..12 — lists every entry the "
                        "range overlaps, the `lines`-style `A..B` grammar; the "
                        "open `Foo:8..` runs to the theory's end, `Foo:..12` "
                        "from its start). "
                        "Pass several to resolve them all in one gate-free "
                        "call, so a batch of build-failure loci needs no "
                        "per-line shell loop.  FILE resolves like "
                        "outline/show — a .thy path or a bare theory name — "
                        "and is scoped by the global -R/--root.")
    g = p.add_mutually_exclusive_group()
    g.add_argument("-e", "--entry", action="store_true",
                   help="report only the owning entry (the outermost block), "
                        "with no proof-internal drill-down")
    g.add_argument("-b", "--blocks", action="store_true",
                   help="report the full nesting path: the entry, then every "
                        "enclosing proof block from outermost to innermost "
                        "(default is the innermost block only)")
    p.set_defaults(func=_run_enclosing)

    # largest
    p = sub.add_parser("largest", help="top N largest entries by span")
    p.add_argument("-N", "--top", type=int, default=20, metavar="N",
                   help="number of entries to show (default 20)")
    _add_path_files_arg(p)  # trailing .thy/dir/name positionals -> union scope
    p.set_defaults(func=_run_largest)

    # find
    p = sub.add_parser("find", help="find entries by name (regex; "
                                    "--statement to match the statement)")
    _add_subject_list_arg(p, cmd="find", dest="pattern", metavar="PATTERN",
                          noun="regex pattern", verb="run each search",
                          extra="matching is case-insensitive")
    _add_mode_flags(p)
    _add_verbatim_flag(p)
    _add_statement_flag(
        p, help_text="match the pattern within each entry's statement slice "
                     "(the declaration, not the proof) instead of its name — "
                     "a token-level `find_theorems`")
    _add_comment_flags(p)
    _add_context_flag(p)
    _add_with_comments_flag(p)
    p.set_defaults(func=_run_find)

    # show
    p = sub.add_parser("show", help="show one or more specific entries")
    _add_subject_list_arg(p, cmd="show",
                          extra="each name is matched exact-then-substring")
    _add_mode_flags(p)
    # `-V` (full slice) and `--statement` (declaration only) are opposite
    # ends of the slice spectrum, so they can't be combined.
    slice_group = p.add_mutually_exclusive_group()
    _add_verbatim_flag(slice_group)
    _add_statement_flag(
        slice_group, help_text="render only the statement slice (the "
                               "declaration, without the proof)")
    _add_comment_flags(p)
    _add_context_flag(p)
    p.set_defaults(func=_run_show)

    # callers
    p = sub.add_parser("callers", help="find proof-body usages")
    _add_subject_list_arg(
        p, cmd="callers",
        extra="\"who calls X\" is corpus-global, so there are no trailing "
              "PATH positionals: scope with the global -R/--root, or cut by "
              "theory boundary with --external")
    _add_count_flag(p)
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect callers)")
    _add_names_flag(p)
    _add_drop_names_flag(p)
    _add_context_flag(p, default=0,
                      help_text="show N trailing lines after each match "
                                "(useful for multi-line `[where ..., OF ...]` "
                                "invocations whose argument list spans 2-3 "
                                "lines; default 0)")
    p.add_argument("--external", action="store_true",
                   help="exclude callers inside the theory that defines "
                        "NAME (e.g. when auditing whether anything outside "
                        "a given theory uses its primitives, that theory's "
                        "own internal cross-references are noise).  Only "
                        "affects the non-recursive form; "
                        "transitive closure via -r ignores this flag.")
    p.set_defaults(func=_run_callers)

    # callees
    p = sub.add_parser("callees",
                       help="entries this entry references; reverse is "
                            "`callers`")
    _add_subject_list_arg(p, cmd="callees")
    _add_count_flag(p)
    _add_names_flag(p)
    _add_drop_names_flag(p)
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect callees)")
    p.add_argument("--external", action="store_true",
                   help="exclude callees defined in NAME's own theory, "
                        "leaving only cross-theory dependencies (mirror of "
                        "`callers --external`).  Only affects the "
                        "non-recursive form; transitive closure via -r "
                        "ignores this flag.")
    p.set_defaults(func=_run_callees)

    # grep
    p = sub.add_parser("grep",
                       help="regex search across live theory source "
                            "(a PATH may carry a `:A..B` line window)")
    p.add_argument("pattern",
                   help="regex pattern (Python syntax; `\\|` rewritten to `|` "
                        "for shell-grep compatibility)")
    _add_path_files_arg(p)
    # grep alone honours a `PATH:A..B` (or `PATH:LINE`) line window on a
    # trailing positional — `query grep PAT Foo.thy:100..200` searches only
    # lines 100-200, the "this token matches hundreds of times, I want one
    # region" case.  Resolved in `_load_sections(windows=True)`; the shared
    # `_add_path_files_arg` help stays window-agnostic (largest/sorry, which
    # also use it, do not accept a window).
    _add_with_comments_flag(p)
    _add_count_flag(p)
    _add_names_flag(p, "locations + owning entry only "
                       "(skip the matched line text)")
    p.set_defaults(func=_run_grep)

    # sorry — located open-goal listing (grep specialised to the sorry token)
    p = sub.add_parser("sorry",
                       help="list open goals: every live `sorry` with its "
                            "location + owning entry")
    _add_path_files_arg(p)
    _add_count_flag(p, "just print the count (build-summary form)")
    p.set_defaults(func=_run_sorry)

    # lines
    p = sub.add_parser("lines",
                       help="print line ranges of FILE with `NR| CONTENT` "
                            "prefix (sandbox-friendly alternative to awk loops)")
    p.add_argument("args", nargs="+", metavar="FILE-or-RANGE",
                   help="either `FILE RANGE...` (`lines Foo 1..10 20..30`) or "
                        "colon-form `FILE:RANGE ...` loci sharing one file "
                        "(`lines Foo:1..10 Foo:20..30`) — the same `FILE:A..B` "
                        "grammar `enclosing` uses, so a span printed elsewhere "
                        "pastes straight in.  FILE is any text file, a bare "
                        "theory name (resolved to its .thy, like outline/show), "
                        "or `-` for stdin (`git show REF:FILE | query lines - "
                        "A..B`).  Each RANGE is `A..B` (inclusive), `A`, or "
                        "open-ended `A..` (to EOF) / `..B` (from line 1); "
                        "multiple ranges are `--`-separated in the output.")
    p.set_defaults(func=_run_lines)

    p = sub.add_parser("unused", help="list entries with zero callers")
    _add_count_flag(p)
    p.add_argument("-r", "--recursive", action="store_true",
                   help="cascade: include entries whose callers are all unused")
    p.add_argument("--by-theory", action="store_true",
                   help="group by theory with line counts")
    p.add_argument("--roots", action="store_true",
                   help="forest summary: each root with exclusive subtree size")
    p.add_argument("--keep", action="append", metavar="NAME[,NAME...]",
                   help="treat these names as live roots (never flag as "
                        "unused, and stop the cascade at them).  Repeatable, "
                        "or pass a comma-separated list.  Use for AFP-headline "
                        "theorems and other intentional zero-caller entries.")
    _add_drop_names_flag(p)
    p.set_defaults(func=_run_unused)

    # methods (alias: method) — proof-method usage; complement of the call
    # graph.  Scopes to a corpus via the global `-R` (e.g. `-R afp/thys`).
    p = sub.add_parser("methods", aliases=["method"],
                       help="proof-method usage tally; `methods NAME` "
                            "(e.g. `methods simp`) lists that method's uses")
    p.add_argument("name", nargs="?", default=None, metavar="NAME",
                   help="a proof method (e.g. simp, auto, induct); omit for "
                        "the ranked tally of every method used")
    _add_mode_flags(p)
    p.set_defaults(func=_run_methods)

    return top


def main():
    global _ROOT_OVERRIDE
    parser = _build_parser()
    ns = parser.parse_args()
    if ns.root:
        _ROOT_OVERRIDE = Path(ns.root).expanduser().resolve()
    if not hasattr(ns, "func"):
        parser.print_help()
        sys.exit(1)
    ns.func(ns)


if __name__ == "__main__":
    main()
