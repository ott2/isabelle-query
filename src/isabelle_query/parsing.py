"""Theory parsing — .thy source into the :class:`~isabelle_query.model.Entry`
database.

The second layer of the module DAG (above ``model``, below everything else).
Everything here is a *pure function of source text*: the declaration grammar
(``DECL_RE`` and the name-extraction helpers), the custom outer-syntax keyword
scanner, span attribution (``compute_spans`` / ``_attach_preambles`` /
``_attach_annotations``), the per-theory parse (``_parse_one`` / ``_parse_plain``),
and the ROOT-walking enumeration (``_sections_from_dir``).  No dependency on
the call graph, rendering, or the CLI, so the whole tree can be parsed without
touching any of them.

Two module globals live here because they belong to the parse:

* ``_CUSTOM_COMMANDS`` — the active root's union of per-header ``keywords``
  tables (Isabelle's session-wide ``Keywords.++``), cleared and rebuilt by
  ``cli.load_index`` before each scan.  It is mutated in place (``.clear()`` /
  ``.update()``), never rebound, so the ``cli`` facade's re-export stays the
  same object.

Note: *which* root to parse (``active_t_dir`` / ``load_index`` / the
``_ROOT_OVERRIDE`` set by ``--root``) is a config concern and stays in ``cli``
— the test suite rebinds ``cli._ROOT_OVERRIDE`` directly, so that binding must
live where the tests reach it.
"""

from __future__ import annotations

import re
from bisect import bisect_right
from collections.abc import Callable, Iterable
from pathlib import Path

from isabelle_layout import (
    SessionInfo,
    discover_roots,
    parse_root_sessions,
    session_theories,
)
from isabelle_query.model import Entry, TheorySection, blank_all

# `(?=\s|$)` (a token boundary), not a consumed `\s`, so a keyword standing
# ALONE on its line — the "name on a following line" form — still matches.
# It stays a whole-word test (`definitions`/`inductively` do not match), and
# being zero-width it leaves the `line[len(keyword):]` slicing untouched.
DECL_RE = re.compile(
    r"^(definition|abbreviation|function|fun|primrec|inductive_set|inductive|lemma|corollary|proposition|theorem|axiomatization|datatype|type_synonym|record|locale|class)(?=\s|$)"
)

TAG_MAP = {
    "definition": "DEF", "abbreviation": "ABBREV",
    "function": "FUN", "fun": "FUN", "primrec": "FUN",
    "inductive_set": "INDSET", "inductive": "IND",
    # `proposition` is `lemma` under another display string: Pure declares
    # `theorem` `lemma` `corollary` `proposition` together on one line as
    # `thy_goal_stmt` (Pure.thy:54) and registers all four through the same
    # combinator, differing only in the word they print (Pure.thy:574-577).
    # It rides with `corollary` — from that same line — rather than with
    # `theorem`, since the LEMMA/THEOREM split here is presentational
    # (`summary`'s two counts) and has no counterpart in Isabelle.
    "lemma": "LEMMA", "corollary": "LEMMA", "proposition": "LEMMA",
    "theorem": "THEOREM",
    "axiomatization": "AXIOM",
    "datatype": "DATATYPE", "type_synonym": "TYPE", "record": "RECORD",
    # A locale/class DECLARES a name — `find hpk` found nothing, and its
    # `assumes` labels (`hpk.commute`) had no entry to hang off.  `context`
    # and `interpretation` are deliberately absent: they REOPEN or INSTANTIATE
    # an existing target rather than declare one.
    "locale": "LOCALE", "class": "CLASS",
}


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
    if tag in ("LOCALE", "CLASS"):
        return "target"
    if tag in ("DATATYPE", "TYPE", "RECORD"):
        return "typedecl"
    if tag in ("LEMMA", "THEOREM"):
        return "goal"
    return "def"  # DEF, ABBREV, FUN, INDSET, IND, and custom thy_decl/thy_defn

PROOF_RE = re.compile(
    r"^\s*(proof\b|by\b|sorry\b|oops\b|using\b"
    r"|unfolding\b|apply\b|\.\.\s*$)"
)
# The same introducers, but anywhere on a line rather than at its start — for
# the one-liner `lemma foo: "P" by simp`, whose proof shares the declaration
# line and so is invisible to a scan that begins on the line BELOW it.
# Applied to the OUTER view of a line, so the `by` of a constant named in a
# term cannot be mistaken for the proof.
_PROOF_INLINE_RE = re.compile(
    r"(?:^|\s)(?:proof\b|by\b|sorry\b|oops\b|using\b"
    r"|unfolding\b|apply\b|\.\.\s*$|\.\s*$)"
)
# Isar keywords that CONTINUE a goal statement.  A long `assumes ... and ...`
# list is often broken up with blank lines for readability, so a blank is not
# reliable evidence that the statement has ended — but one of these starting
# the next line is reliable evidence that it has not.
_STATEMENT_CONT_RE = re.compile(
    r"^\s*(?:and|shows|assumes|fixes|obtains|defines|notes"
    r"|where|if|for)\b")


BLANK_RE = re.compile(r"^\s*$")
TOPLEVEL_RE = re.compile(r"^[a-z]")
# A declared name in `axiomatization`, on either side of its `where`: a constant
# (`f :: "nat"`) or an axiom label (`ax1: "P"`), both read off the colon.  A full
# Isabelle identifier, not `[a-z_]+` — a label may start with a capital, and may
# carry digits or primes, none of which are unusual (`ax1`, `f'`).
_AXIOM_NAME_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_']*)\s*:")
# The heading commands, taken from Isabelle's own keyword table rather than
# listed from memory: `_isabelle_namespace.KEYWORDS` (extracted from a running
# Isabelle2025-2) carries `paragraph` and `subparagraph` beside the familiar
# four, and 888 AFP headings use them.  It does *not* carry `section*` —
# Isabelle_DOF's `section*[label::type]` is that session's own command, not base
# syntax, so accepting it here would be inventing a command.
_HEADING_WORDS = r"chapter|section|subsection|subsubsection|paragraph|subparagraph"
# The opener of a heading's title.  Three spellings, all of them written: both
# cartouches and a plain quoted string, which is `text`-argument syntax too
# (3,980 AFP headings, e.g. `section "Preliminary lemmas"`).
_TITLE_OPEN = r'\\<open>|‹|"'
# The heading COMMAND; its title is matched separately by `_TITLE_OPEN_RE`,
# because a document marker may sit between the two
# (`subsection\<^marker>\<open>tag unimportant\<close> \<open>Norm\<close>`) and a
# marker body may itself hold a cartouche, which no regex can balance.
#
# ONE recogniser (`_heading_at`) is built on this, shared by everything that
# asks "is this line a heading?" — `outline`'s view, the prose mask, and the
# proof extent.  There were once two patterns, tight and wide respectively, on
# the reasoning that a view wants no false positives while a mask cannot afford
# a false negative.  Both instincts are right in isolation and the conclusion
# was wrong: a heading is a heading, so the recogniser is a fact about Isar, not
# about the consumer.  Disagreeing cost `outline` 14,238 AFP headings it never
# showed [heading-outline].  Leading indent is allowed and no space is required
# before the opener, because Isar is whitespace-insensitive and both are
# written.  The negative lookahead is what a combined pattern got implicitly
# from demanding an opener next: without it `sections` would lead with
# `section`.
_HEADING_LEAD_RE = re.compile(rf"^\s*({_HEADING_WORDS})(?![A-Za-z_0-9'])")
_TITLE_OPEN_RE = re.compile(rf"^\s*({_TITLE_OPEN})(.*)")
# What closes each opener.  Quotes are their own close, which is why the quoted
# form needs a counting scan rather than the balancing one.
_TITLE_CLOSE = {"\\<open>": "\\<close>", "‹": "›", '"': '"'}
# An unescaped `"` — the delimiter of the quoted title form.
_UNESCAPED_QUOTE_RE = re.compile(r'(?<!\\)"')
# Isabelle's document commands, whose bodies are prose rather than Isar.  `txt`
# is the *in-proof* one — it appears between proof steps, where `text` appears
# between declarations — and omitting it meant a step scanner read its English
# as tactics.  No `txt_raw`: it is not a keyword in Isabelle2025-2 (it is absent
# from `_isabelle_namespace.KEYWORDS`, extracted from a running Isabelle) and has
# no occurrence in the AFP, so accepting it would be inventing a command.
# Both cartouche spellings, as `COMMENT_LINE_RE` does — neither `text ‹...›` nor
# `txt ‹...›` occurs in the AFP, but recognising one spelling and not the other
# is a leak waiting for the project that prefers it.
TEXT_OPEN_RE = re.compile(r"^\s*(text|text_raw|txt)\s*(?:\\<open>|‹)")
# The same commands with nothing after them: the cartouche is on the next line.
# Used only with that lookahead — see `extract_text_blocks`.
_TEXT_BARE_RE = re.compile(r"^\s*(text|text_raw|txt)\s*$")
# Both cartouche spellings, so this agrees with the tokenizer's
# `_MARKER_OPEN_RE` — a note it recognises is a note this extracts.
COMMENT_LINE_RE = re.compile(r"\\<comment>\s*(?:\\<open>|‹)(.*)$")
LATEX_LINE_RE = re.compile(
    r"\\(begin|end|caption|node|draw|newlength|newcommand|settowidth|settoheight|scalebox|label)\b"
)
# Isabelle fact/definition names that contain non-identifier characters
# (-, :, [, ], digits after a colon, ...) must be double-quoted at their
# declaration site, e.g. `theorem "beta-C-cor:3":`.  Capture the quoted
# spelling verbatim so `show`/`callers` can find the entry by the name the
# source actually uses.
QUOTED_NAME_RE = re.compile(r'^"([^"]+)"')
# Isabelle's FORMAL COMMENTS: a marginal note, deleted text, raw LaTeX and a
# document-build marker.  Each owns the cartouche that follows it, and none of
# the four is live Isar — Isabelle's lexer skips them wherever a token may
# appear, which is why one can sit glued to a command keyword
# (`definition\<^marker>\<open>tag important\<close> istopology`) or in a name
# slot.  Listed once and used twice: the tokenizer redacts exactly these
# (`_REDACTING_MARKERS`), and none of them is a name character.
_MARGINAL = "\\<comment>"
_CANCEL = "\\<^cancel>"
_LATEX = "\\<^latex>"
_MARKER = "\\<^marker>"
FORMAL_COMMENTS = (_MARGINAL, _CANCEL, _LATEX, _MARKER)
# The symbols that are STRUCTURE rather than name characters: the two cartouche
# delimiters and the four formal comments.  Each can sit where a name is
# expected — a cartouche statement, an annotation, a document marker — and must
# not be captured as one.
RESERVED_NAME_PREFIXES = ("\\<open>", "\\<close>") + FORMAL_COMMENTS

# A bare name may interleave ASCII identifier characters with Isabelle
# symbol tokens written `\<...>` (e.g. \<psi>, \<alpha>ah, \<tau>rtrancl3p)
# and subscript controls (\<^sub>1).  Treating `\<...>` runs as name
# characters captures the many AFP entries whose names are Greek letters or
# decorated identifiers, which a plain `\w[\w']*` pattern misses.
#
# TWO questions, so two atoms.  `ISA_SYMBOL` is LEXICAL — is this an Isabelle
# symbol token? — and `ISA_MARKUP` is GRAMMATICAL: may this token occur inside a
# NAME?  They differ by exactly `RESERVED_NAME_PREFIXES`.  Conflating them let a
# name run straight through a structural symbol, so
# `coprod_final_sink\<^marker>\<open>tag` was indexed as one name.
#
# Which one a scanner wants follows from what it is doing, and the split is not
# cosmetic in either direction:
#
#   * a RUN scanner (`graph`'s citation tokens, `shape`'s token counter) asks
#     only where a token ends, over source the tokenizer has already redacted.
#     It wants the lexical atom.  Narrowing it there does not help and actively
#     harms: `\<open>foo` would stop being one run and start yielding `open` as
#     a candidate fact name, and `\<comment>` would count as ten tokens rather
#     than one;
#   * a NAME scanner (below, plus the datatype and target grammars) reads RAW
#     source, where a marker really can abut the name, and must stop at it.
#
# Everything is built from these rather than respelling them: the atom was
# written out eight times across `parsing`, `graph`, `shape` and `commands`,
# which is eight places to update when the lexical fact changes and eight
# chances for one of them to drift.  Where a regex below still differs, the
# difference is deliberate and commented — a target name admits `.`, an entry
# name does not.
ISA_SYMBOL = r"\\<\^?\w+>"
_NOT_STRUCTURAL = "(?!" + "|".join(
    re.escape(s[len("\\<"):]) for s in RESERVED_NAME_PREFIXES) + ")"
ISA_MARKUP = rf"\\<{_NOT_STRUCTURAL}\^?\w+>"
# One character of a symbol RUN (lexical) / of a NAME (grammatical).
ISA_WORD_CHAR = rf"(?:{ISA_SYMBOL}|[\w'])"
ISA_NAME_CHAR = rf"(?:{ISA_MARKUP}|[\w'])"
SYM_NAME_RE = re.compile(rf"((?:{ISA_MARKUP}|\w){ISA_NAME_CHAR}*)")
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

# A named rule/equation of a `where`-clause declaration: after `where` or a
# top-level `|`, an identifier with optional [attributes], then a single `:`
# — never the `::` of a type ascription, a guard that is defensive rather than
# load-bearing (dropping it changes nothing over 120 AFP entries: 547 labels
# either way, because the built-in grammar puts every `::` after a name in the
# head, before `where`) and is kept for the custom `thy_decl` commands that
# take this route with a grammar of their own.  `inductive p where r1: "..." | r2:
# "..."` binds r1 and r2 as citable facts — and for an inductive predicate
# those ARE how it gets cited, so the loss is concentrated exactly where the
# citations are.
#
# The grammar is not special to `inductive`: over 120 AFP entries the same
# shape carries 70 `primrec` equation names, 17 `definition`s
# (`definition F where eq_fold: "..."`), 14 `fun` and 6 `function` — so this is
# scanned for every `def`-route command, not just the inductive family.
#
# Applied to the OUTER view, where inner syntax is blanked, so a `|` or an
# `x:` inside a term (or inside a mixfix template) cannot be read as a rule
# separator or a label.  And only over a declaration's own extent: the same
# shape inside a PROOF is `obtain S' where S: "..."`, a local Isar fact and
# not a theory-level name, which is why the `goal` route does not scan for it.
RULE_LABEL_RE = re.compile(
    r"(?:(?<![\w'])where(?![\w'])|\|)\s*"
    r"([A-Za-z][\w']*)\s*(?:\[[^\]]*\])?\s*:(?!:)")


def _rule_labels(outer: list[str], start: int, end: int,
                 own: str) -> list[str]:
    """Named rules/equations declared in `outer[start-1:end]` (1-indexed,
    inclusive), in source order, without duplicates or the entry's own name."""
    if start < 1 or end < start:
        return []
    found: list[str] = []
    for m in RULE_LABEL_RE.finditer("\n".join(outer[start - 1:end])):
        label = m.group(1)
        if label != own and label not in found:
            found.append(label)
    return found


# A rule/equation list continued after a gap.  Asked of the OUTER view, which
# already draws the line this needs: a blank and a `(* ... *)` comment blank to
# nothing, while `text \<open>...\<close>` keeps its command word.  So the
# lookahead steps over formatting and notes — `OAWN_SOS:222` spaces its rules
# apart AND puts a comment between two of them — but stops at anything that is
# structure, which must end the declaration on its own terms.
_BAR_LINE_RE = re.compile(r"^\s*\|")


def _bar_continues(outer: list[str], i: int) -> bool:
    """Does the next line carrying outer syntax, at or after `i`, begin `|`?"""
    while i < len(outer) and not outer[i].strip():
        i += 1
    return i < len(outer) and bool(_BAR_LINE_RE.match(outer[i]))


def _field_continues(outer: list[str], live: list[str], i: int) -> bool:
    r"""Does the next line carrying outer syntax, at or after `i`, declare a
    `record` field?

    A record's field list has no `|` to pick it back up after a blank line, so
    `_bar_continues` cannot serve it; the marker is the field's own `::`.  The
    Lem-generated CakeML theories write every record that way —

        record 'a NumNegate_class=

          numNegate_method ::" 'a \<Rightarrow> 'a "

    — and the blank line ended the body scan, so 32 of the AFP's 507 records
    (6.3%) reported no fields at all.  Same shape of bug as the `|` one, same
    shape of fix; layout carries no meaning either way.

    Both views, for the reason `_record_fields` needs both: a quoted field name
    is blanked on the outer one, and `SatSolverCode:22` writes every field that
    way.  Skipping blank lines here is `_bar_continues`' rule, not a new one.
    """
    while i < len(outer) and not outer[i].strip() and not live[i].strip():
        i += 1
    return i < len(outer) and bool(
        _RECORD_FIELD_RE.search(outer[i])
        or _RECORD_QUOTED_FIELD_RE.search(live[i]))


# `and`-separated constants in a declaration HEAD: `fun f and g and h where
# ...` declares three, and only the first was recorded.  Same for `function` /
# `primrec` / `inductive` / `inductive_set`.
#
# The head ends at `where` OR at `for`, and the `for` is the trap: `inductive_set
# p for A :: "..." and I :: "..."` fixes PARAMETERS with `and`, so a scan that
# cuts only at `where` reads every `for` clause as a list of siblings.
#
# Gated on the TAG, not on the `def` route, because an `and`-list is a property
# of particular Isabelle commands rather than of definitional syntax at large:
# `definition` and `abbreviation` do not take one.  The gate also excludes
# custom commands by construction — `_KIND_FAMILY` only ever maps a declared
# keyword to DEF or THEOREM — and that matters: AOT's `AOT_register_type_
# constraints Individual: ... and Proposition: ...` reads as a sibling list,
# but its `and`s separate type-constraint categories, not constants.  A custom
# command's grammar is its own, so it must not be guessed at.
_SIBLING_TAGS = frozenset({"FUN", "IND", "INDSET"})
_HEAD_END_RE = re.compile(r"(?<![\w'])(?:where|for)(?![\w'])")
# `and NAME`, where NAME may be quoted (a constant whose spelling needs it).
_AND_NAME_RE = re.compile(
    r"(?<![\w'])and(?![\w'])\s*(?:\"([^\"\n]+)\"|([A-Za-z][\w']*))")


# The names a `datatype` alternative declares.  In
#
#     datatype 'ent atom = is_p: predAtm (predicate: predicate) (args: "'ent list")
#                        | Eq (lhs: 'ent) (rhs: 'ent)
#
# the alternatives declare constructors `predAtm`/`Eq`, `predAtm`'s
# discriminator `is_p`, and the selectors `predicate`/`args`/`lhs`/`rhs` — all
# real constants, all citable, none of them the datatype's own name.
#
# Built from the same symbol-aware name fragment the rest of the parser uses,
# because a constructor is routinely spelled with markup: `View\<^sub>m` reads
# as `View` under a plain `[A-Za-z][\w']*`, which would index the wrong name.
_ISA_NAME = rf"(?:{ISA_MARKUP}|[A-Za-z]){ISA_NAME_CHAR}*"
# `disc: Ctor` at the head of an alternative; the `disc:` part is optional.
_ALT_HEAD_RE = re.compile(rf"^\s*(?:({_ISA_NAME})\s*:(?!:)\s*)?({_ISA_NAME})")
# `(sel: type)` anywhere in the alternative's argument list.  The `(?!:)` is
# defensive, like the rule scan's: BNF writes a selector with one colon and a
# type ascription cannot appear here, so dropping it changes nothing over 120
# AFP entries (176 selectors either way).
_SELECTOR_RE = re.compile(rf"\(\s*({_ISA_NAME})\s*:(?!:)")
# A `record` field: `name :: type`, one per field.  Read on the outer view,
# where the type — inner syntax — is already blanked, so the only `::` left in
# a record's span is a field's own.  That is what makes this a two-token scan
# rather than a grammar: the head declares no `::` (`record ('a,'b) r =`), and
# neither does the parent clause, quoted (`= "'a TS" +`) or bare
# (`= opt_obsv_state +`).
_RECORD_FIELD_RE = re.compile(rf"(?<![\w'])({_ISA_NAME})\s*::")
# ...and the same field with a QUOTED name, which the outer view blanks along
# with every other quoted span — `record State = "getM" :: LiteralTrail`,
# `record "globals" = "G_'" :: "nat"`.  A field is quoted for the usual reason,
# that its spelling would not pass as a bare identifier.  Read on the LIVE view
# instead, the same way a quoted locale name is; safe there because a *type*
# never contains a quoted string, so a `"..." ::` can only be a field.
_RECORD_QUOTED_FIELD_RE = re.compile(r'"([^"\n]+)"\s*::')


def _entries_by_line(
        entries: list[Entry]) -> tuple[list[tuple[int, Entry]], list[int]]:
    """Located entries ordered by source line, plus the bare line keys.

    The keys are returned alongside because both callers bisect them; building
    the pair once keeps the two lists provably in step.

    Sorted on the line **alone**.  Two entries may share a `thy_line` — an
    `axiomatization` whose command line already carries a name declares both
    the umbrella and that name there — and sorting the tuples themselves would
    fall through to comparing `Entry`s, which are not orderable, raising
    `TypeError` mid-parse.  `sorted` is stable, so a tie keeps source order:
    the innermost/most specific entry on a line is the last of its group, which
    is the one `bisect_right(...) - 1` selects as a comment's owner.
    """
    pairs = sorted([(e.thy_line, e) for e in entries if e.thy_line > 0],
                   key=lambda pair: pair[0])
    return pairs, [line for line, _ in pairs]


# `and` at outer-syntax position, separating two items of one `axiomatization`.
# Only ever applied to the OUTER view, so the `and` inside a proposition — or
# the `\<and>` connective, whose letters this would otherwise match — is already
# blanked.
_AXIOM_AND_RE = re.compile(r"(?<![\w'])and(?![\w'])")


def _axiom_line(text: str) -> tuple[list[str], bool]:
    """Read one `axiomatization` line: the names it declares, and whether it
    opened with a continuation keyword.

    *Names*, plural, because `and` separates items **within** a line as
    readily as it ends one:

        axiomatization f :: "nat" and g :: "nat"
        where ax1: "f 0 = 0" and ax2: "g 0 = 0"

    declares four things on two lines, and reading only the first of each lost
    half of them.  The scan therefore steps item by item — name, next `and`,
    name — rather than matching once at the start of the line.

    `text` must be the OUTER view of the line, so a colon inside a proposition
    cannot be mistaken for a label — the same discipline `_constructors` uses,
    for the same reason.

    `where` separates the constants from the axioms about them, and `and`
    separates items within either part; both continue the *same* command.
    Either may also share a line with the item it introduces
    (`where ax1: "P"`, `and cp0_contents: "..."`), so strip the keyword and
    look again rather than skipping the line.  The second return value matters
    because a line that is *only* `where` must not end the scan: unindented it
    matches `TOPLEVEL_RE` (`^[a-z]`), which read it as the next command and
    dropped every labelled axiom that followed.
    """
    stripped = text.strip()
    cont = bool(_STATEMENT_CONT_RE.match(stripped))
    names: list[str] = []
    while stripped:
        kw = _STATEMENT_CONT_RE.match(stripped)
        if kw:                       # `where` / `and` / ... introducing an item
            stripped = stripped[kw.end():].lstrip()
            continue
        m = _AXIOM_NAME_RE.match(stripped)
        if not m:
            break
        names.append(m.group(1))
        nxt = _AXIOM_AND_RE.search(stripped, m.end())
        if not nxt:                  # nothing further on this line
            break
        stripped = stripped[nxt.end():].lstrip()
    return names, cont


def _constructors(outer: list[str], start: int, end: int,
                  own: str) -> list[tuple[str, str]]:
    """`(name, kind)` for the constructors, discriminators and selectors a
    `datatype` declares, in source order.

    Read on the outer view, so a constructor's argument TYPES — inner syntax,
    and full of names that are not constructors — are blanked before the scan,
    and a quoted mixfix template cannot contribute an alternative.

    A `record`'s fields are NOT read here: `record point = parent + x :: nat`
    uses `=` for the parent-type clause and declares fields as bare
    `name :: type` lines, a different grammar with its own scan — see
    `_record_fields`.  Pointed at a record, this one reads the parent type as a
    constructor.
    """
    if start < 1 or end < start:
        return []
    text = "\n".join(outer[start - 1:end])
    if "=" not in text:
        return []                      # `datatype` with no alternatives given
    found: list[tuple[str, str]] = []
    seen = {own}

    def add(name: str | None, kind: str) -> None:
        if name and name not in seen:
            seen.add(name)
            found.append((name, kind))

    for alt in text.split("=", 1)[1].split("|"):
        m = _ALT_HEAD_RE.match(alt)
        if not m:
            continue
        add(m.group(1), "discriminator")
        add(m.group(2), "constructor")
        for s in _SELECTOR_RE.finditer(alt):
            add(s.group(1), "selector")
    return found


def _record_fields(outer: list[str], live: list[str], start: int,
                   end: int) -> list[tuple[str, str]]:
    r"""`(name, "field")` for the selector constants a `record` declares.

        record ('n,'p,'ba) flowgraph_rec =
          edges :: "('n,'p,'ba) edge set"  \<comment> \<open>annotated edges\<close>
          main  :: "'p"

    declares the constants `edges` and `main` — total selector functions on the
    record type, cited everywhere the record is used, and until now indexed
    nowhere.  522 records in the AFP.

    A separate scan from `_constructors`, not a widening of it, because the two
    grammars collide on `=`: a datatype's `=` introduces its alternatives, a
    record's introduces its *parent type*, so pointing the alternative scan at a
    record would read the parent as a constructor.  Fields are bare
    `name :: type` items with no `|` between them, which is the other half of
    why one scan cannot serve both.

    Read on the outer view for the usual reason — a field's type is inner
    syntax, and `"('n,'p,'ba) edge set"` is full of names that are not fields —
    with the quoted spelling picked up from the live view, which is the one
    place that blanking hides the name rather than the noise.  Both views are
    character-aligned (blanking substitutes spaces), so the two sets of hits
    merge on `(line, column)` and the result is still in source order.

    Unlike `_constructors` this does NOT exclude the declaration's own name:
    `Algebra1:4600` writes `record 'a carrier = carrier :: "'a set"`, and the
    type `carrier` and the selector `carrier` are different things in different
    namespaces.  A datatype's `datatype 'a t = t ...` is the opposite case — one
    namespace, so the constructor named for its type is excluded there.
    """
    if start < 1 or end < start:
        return []
    hits: list[tuple[int, int, str]] = []
    for n in range(start - 1, min(end, len(outer))):
        # Line by line, NOT over the joined span: `\s*` matches a newline, so a
        # scan of the joined text pairs an unquoted type at the end of one line
        # with the `::` of the next — `"getSATFlag" :: ExtendedBool` followed by
        # a `\<comment>` line (blank on the outer view) and `"getF" :: Formula`
        # declared a field called `ExtendedBool`.  A field's name and its `::`
        # are on one line in every AFP record.
        for m in _RECORD_FIELD_RE.finditer(outer[n]):
            hits.append((n, m.start(1), m.group(1)))
        for m in _RECORD_QUOTED_FIELD_RE.finditer(live[n]):
            hits.append((n, m.start(1), m.group(1)))
    found: list[tuple[str, str]] = []
    seen: set[str] = set()
    for _ln, _col, name in sorted(hits):
        if name not in seen:
            seen.add(name)
            found.append((name, "field"))
    return found


# The named facts a locale/class head binds.  `locale L = fixes x assumes
# a: "P" and b: "Q"` binds `L.a` and `L.b`, cited constantly inside the locale
# and never indexed.  `defines` and `notes` bind by the same shape, so the
# introducing keyword is captured and carried: an assumption is not a
# definition is not a note.
#
# `fixes`, `constrains` and `for` bind PARAMETERS rather than facts, and they
# are listed so they RESET the current element: Isabelle allows a second
# `fixes` group after an `assumes` (`Akra_Bazzi_Real:501` writes
# `fixes ... assumes integral: ... fixes g :: ... and C :: real`), and without
# the reset that trailing `and C` inherits "assumption" and binds a parameter
# as a fact.
_LOCALE_KW_RE = re.compile(
    r"(?<![\w'])(assumes|defines|notes|fixes|constrains|for|and)(?![\w'])")
# The label a locale element may carry, matched immediately after its keyword —
# anchored there, not searched for, or an unnamed `assumes` picks up the label
# of whatever element comes next and files it under the wrong kind.
#
# The single-colon requirement is a second line of defence and, with the reset
# above in place, a redundant one: 1,830 elements either way over 120 AFP
# entries.  Kept because it states the grammar (`g :: "T"` is a parameter, not
# a label) rather than relying on the reset to be exhaustive.
_LOCALE_LABEL_RE = re.compile(r"\s*([A-Za-z][\w']*)\s*(?:\[[^\]]*\])?\s*:(?!:)")
_LOCALE_ELEM_KIND = {"assumes": "assumption", "defines": "definition",
                     "notes": "note"}


def _locale_facts(outer: list[str], start: int, end: int,
                  own: str) -> list[tuple[str, str]]:
    """`(name, kind)` for each named element of a locale/class head.

    An `and` continues whichever element introduced it, so the last non-`and`
    keyword decides the kind — and a parameter-binding keyword clears it, so
    the `and`s of a `fixes` group bind nothing.
    """
    if start < 1 or end < start:
        return []
    found: list[tuple[str, str]] = []
    seen = {own}
    current = ""
    text = "\n".join(outer[start - 1:end])
    for m in _LOCALE_KW_RE.finditer(text):
        kw = m.group(1)
        if kw != "and":
            current = _LOCALE_ELEM_KIND.get(kw, "")
        if not current:
            continue
        label = _LOCALE_LABEL_RE.match(text, m.end())
        if label is None or label.group(1) in seen:
            continue
        seen.add(label.group(1))
        found.append((label.group(1), current))
    return found


def _scan_decl_body(lines: list[str], outer: list[str], live: list[str],
                    open_at: list[bool],
                    table: dict[str, str], i: int, decl_line: int,
                    keyword: str = "") -> tuple[int, int, list[str]]:
    """Accumulate a declaration's body from line index `i` (0-indexed, the
    line after the declaration line).

    Returns `(next index, decl_end_line, body lines)`.  Shared by the `def` and
    `typedecl` routes: what ends a `datatype` is what ends a `fun`, and the two
    had drifted — `typedecl` did not scan at all.
    """
    decl_end_line = decl_line
    body: list[str] = []
    past_where = False  # for `definition`/`abbreviation`: tracks whether the
                        # body's quoted RHS has begun, so we don't break at the
                        # type signature's closing quote.
    while i < len(lines):
        cline = lines[i]
        # Nothing terminates a declaration from INSIDE its own term.  A
        # `do { ... }` definition body is routinely written with blank lines
        # between its rounds and annotated line by line, and both used to cut
        # the declaration short.
        inside = open_at[i]
        if BLANK_RE.match(cline) and not inside:
            # ...unless a `|` picks the rule list back up.  A rule or equation
            # list is routinely spaced out for legibility, and a line beginning
            # `|` cannot start a new command, so it can only continue this one.
            # `AWN_SOS:14`'s `inductive_set seqp_sos` runs to line 34 and used
            # to end at 26; `Aodv:264`'s `fun` runs to 420 and ended at 300.
            #
            # A `record` has no `|` between its fields, so its continuation
            # marker is the field's own `::` — see `_field_continues`.  Gated on
            # the keyword because `name ::` after a blank line means something
            # else everywhere else: it is a fresh `fixes`/`assumes` item, or the
            # signature of the *next* declaration.
            # ...and unless nothing of the declaration has been seen yet.  A
            # blank cannot END what has not STARTED, and a keyword standing
            # alone above its name is routinely spaced: `WFair:35` is
            # `definition`, a blank, a four-line note, then `transient ::`.
            # Without this the blank breaks before the note is even reached,
            # so the note skip below never runs [decl-body-comment].  Bounded
            # exactly as before by the declaration and boundary checks, which
            # come first; with no body to append, a run of blanks leaves
            # `decl_end_line` on the keyword line either way.
            if not (_bar_continues(outer, i + 1)
                    or (keyword == "record"
                        and _field_continues(outer, live, i + 1))):
                break
            i += 1
            continue
        if _match_decl_at(outer[i], table)[0] \
                or (not inside and _is_boundary_at(outer[i])):
            break
        stripped = cline.strip()
        if not inside and stripped.startswith("text "):
            break
        # A formal comment is not a command — Isabelle's lexer skips all four
        # of them wherever a token may appear — so one cannot END a declaration
        # either, on any route.  Skip it and keep scanning [decl-body-comment].
        #
        # This was a `break` gated to `record`, where breaking cost 11 of the
        # AFP's 507 records every field they declare; the gate was left narrow
        # because "whether the break is right for the other routes ... has not
        # been measured, and widening on the strength of this case would be a
        # guess".  Measured now (`scripts/probe_comment_split_scale.py`): the
        # break truncates 50 declarations over 11,514 theories, every one of
        # the keyword-comment-name shape, where the comment sits before the
        # name and the recorded body collapses onto the keyword line —
        # `SchorrWaite:14`'s `rel` reported `body 14..14` for a declaration
        # running to 17.  `body_end_line` is the documented "safe relocation
        # cut" and now `api` surface, so a consumer cutting there leaves the
        # declaration behind.
        #
        # Asking the live view rather than testing for a leading `\<comment>`
        # is what makes this cover a WRAPPED comment (only its first line
        # carries the marker), the other three spellings, and `(* ... *)` —
        # the same correction as `_lookahead_name`'s [comment-before-name].
        # The comment is skipped rather than appended, so `decl_end_line` still
        # ends on the last LIVE line and a trailing note does not extend it.
        # Running on into the next declaration is not a risk: `_match_decl_at`
        # and `_is_boundary_at` above already break there.
        if not inside and stripped and not live[i].strip():
            i += 1
            continue
        where_on_this_line = bool(re.search(r"\bwhere\b", stripped))
        body.append(f"  {stripped}")
        i += 1
        decl_end_line = i  # 1-indexed line just appended
        if keyword in ("definition", "abbreviation"):
            # The body's quoted RHS has closed when the NEXT line no longer
            # begins inside a term.  This was a hand-rolled quote parity that
            # could not see escapes or cartouches.
            if past_where and '"' in stripped \
                    and not (i < len(lines) and open_at[i]):
                break
            if where_on_this_line:
                past_where = True
    return i, decl_end_line, body


def _and_siblings(outer: list[str], start: int, end: int, own: str,
                  tag: str) -> list[str]:
    """Constants declared alongside `own` by one command, in source order.

    Read from the head only — everything before the first `where`/`for` — on
    the outer view, so an `and` inside a term or a mixfix template is invisible.
    Empty unless `tag` is one of the commands that takes an `and`-list.
    """
    if start < 1 or end < start or tag not in _SIBLING_TAGS:
        return []
    head = "\n".join(outer[start - 1:end])
    cut = _HEAD_END_RE.search(head)
    if cut:
        head = head[:cut.start()]
    found: list[str] = []
    for m in _AND_NAME_RE.finditer(head):
        name = m.group(1) or m.group(2)
        if name != own and name not in found:
            found.append(name)
    return found


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
      because Isabelle allows `'` inside identifiers (`foo'`), plus a guard
      against the SYMBOL BODY.  A plain run also sits between non-`[\w']`
      characters when it is the inside of a `\<...>` token, so `lambda` matched
      within `\<lambda>`, `le` within `\<le>` and `sub` within `\<^sub>` — and
      the AFP declares 7 entries named `lambda`, 37 named `le` and 27 named
      `sub` [symbol-body-tokens].  The two lookbehinds are the single-name form
      of what `graph._build_call_graph` does by blanking symbol tokens before
      its word pass; a symbol's body is that symbol's name, never a fact's.
    """
    if _SPECIAL_NAME_RE.search(name):
        return r'(?<=")' + re.escape(name) + r'(?=")'
    left = r"(?<![\w'])" + (r"(?<!>)" if name.startswith("\\<")
                            else r"(?<!\\<)(?<!\\<\^)")
    right = (r"(?!\\<)" if name.endswith(">") else "") + r"(?![\w'])"
    return left + re.escape(name) + right


def _balanced_end(s: str, open_tok: str, close_tok: str, *,
                  start: int = 0, quote_aware: bool = False) -> int:
    r"""Index in ``s`` just past the ``close_tok`` matching the ``open_tok`` that
    ``s[start:]`` opens with; ``-1`` if the delimiter never closes on this text.

    The package's single balanced-delimiter scanner.  A depth counter is a
    one-symbol pushdown automaton — the least machinery a *non-regular* nesting
    construct needs, and precisely what a regular expression cannot supply — so
    every place that must respect Isar nesting routes through here rather than
    re-rolling the loop.  Parameterising the token pair lets one scanner serve
    both the character paren ``(``/``)`` and the multi-byte symbol cartouche
    ``\<open>``/``\<close>`` (which nest alike); ``str.startswith`` — not ``==`` —
    is what makes a multi-character delimiter a token like any other.  With
    ``quote_aware`` a delimiter inside a ``"..."`` term is ignored, where a stray
    paren is data, not structure."""
    depth = 0
    i, n = start, len(s)
    in_quote = False
    while i < n:
        if quote_aware and s[i] == '"':
            in_quote = not in_quote
            i += 1
        elif in_quote:
            i += 1
        elif s.startswith(open_tok, i):
            depth += 1
            i += len(open_tok)
        elif s.startswith(close_tok, i):
            depth -= 1
            i += len(close_tok)
            if depth == 0:
                return i
        else:
            i += 1
    return -1


def _balanced_paren_end(s: str) -> int:
    """Index just past the ')' matching a leading '(' (s must start with
    '('), accounting for nesting; -1 if unbalanced.  The intention-revealing
    name for the common case — a thin façade over :func:`_balanced_end`."""
    return _balanced_end(s, "(", ")")


def _balanced_cartouche_end(s: str) -> int:
    r"""Index just past the `\<close>` matching a leading `\<open>` (s must
    start with `\<open>`), accounting for nesting; -1 if unbalanced (e.g. a
    cartouche that runs past the end of this line).  The cartouche is the
    symbol-level analogue of a paren, so it is the same :func:`_balanced_end`
    scan with the `\<open>`/`\<close>` token pair."""
    return _balanced_end(s, "\\<open>", "\\<close>")


def _skip_formal_comments(s: str) -> str:
    r"""``s.lstrip()`` with every leading formal comment removed, along with the
    cartouche each of them owns.

    Isabelle's lexer skips all four of `FORMAL_COMMENTS` wherever a token may
    appear, so this is what stands between a command keyword and the thing that
    actually follows it — a declaration's name, or a heading's title.  Written
    once for both: they are the same grammatical position.

    Balanced, not "to the first ``\<close>``": a marker body may itself hold a
    cartouche, as `First_Order_Terms/Term:37`'s
    ``\<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>`` does.
    A comment that runs past the end of this line stops the scan, leaving it in
    place — the caller sees an unparseable rest rather than a wrong answer.
    """
    s = s.lstrip()
    while s:
        marker = next((m for m in FORMAL_COMMENTS if s.startswith(m)), None)
        if marker is None:
            break
        rest = s[len(marker):].lstrip()
        if rest.startswith("\\<open>"):
            k = _balanced_cartouche_end(rest)
            if k < 0:
                break                   # comment runs past this line
            rest = rest[k:].lstrip()
        s = rest
    return s


def _strip_decl_prefix(s: str, typevars: bool) -> str:
    r"""Drop the syntactic noise that can sit between a keyword and the name.

    A fact or type name never starts with '(', a type variable, or a formal
    comment, so this only removes:
      * command modifiers / locale specs — ``(in foo)``, ``(nonexhaustive)``,
        ``(overloaded)``, ``(discs_sels)``, ``(sequential)``, ...
      * a leading formal comment — ``\<comment> \<open>...\<close>`` annotating
        the declaration before its name, or the document marker
        ``\<^marker>\<open>tag important\<close>`` that `HOL/Analysis` writes on
        hundreds of them.  All four spellings, since Isabelle's lexer skips all
        four in the same place;
      * for type declarations (``typevars=True``), leading type arguments,
        either bare (``'a``) or grouped (``('a, 'b)``).

    The marker is stripped here as well as blanked by the tokenizer because
    this reads the RAW line: recognition uses the outer view (where the marker
    is already gone), but a name can live inside a term, so extraction cannot.
    """
    while s:
        if s[0] == "(":
            j = _balanced_paren_end(s)
            if j < 0:
                break
            s = s[j:].lstrip()
            continue
        skipped = _skip_formal_comments(s)
        if skipped != s:
            s = skipped
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
    from a glued `::thy_goal`'s tail, or from a quoted `"thy_goal"`)."""
    m = re.match(r'"?([A-Za-z_]+)', tok)
    return m.group(1) if m else ""


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
                # The kind is the first token after `::`, quoted or not —
                # Isabelle's grammar reads it as a *name*, and Optics writes
                # `:: "thy_defn"`.  Quoting only distinguishes a command name
                # from a `% tag` value BEFORE the colon; past it the slot
                # decides.  `not kind` is what still keeps a quoted tag value
                # out: by the time `% "proof"` arrives the kind is bound.
                if not kind:                   # the kind, just after `::`
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


def _is_boundary_at(outer_line: str) -> bool:
    """Does this OUTER-syntax line open a span-bounding command?

    The terminator a declaration scan actually wants.  A blank line ends
    nothing in Isar — it is whitespace — but `end`, `context`, `lemmas`,
    `declare`, an `ML` block and the rest of `_SPAN_BOUNDARY_COMMANDS` all
    genuinely close whatever preceded them.
    """
    m = _LEADING_CMD_RE.match(outer_line.lstrip())
    return m is not None and m.group(1) in _SPAN_BOUNDARY_COMMANDS


def _match_decl_at(outer_line: str, table: dict[str, str]
                   ) -> tuple[tuple[str, str, str] | None, int]:
    """:func:`_match_decl` on the first command token of an OUTER-syntax line.

    Returns ``(match, indent)`` — `indent` being the column the keyword starts
    at, so a caller can slice the RAW line at the same offset and read what the
    command says.  The two views are length-preserving, so one index serves
    both.

    This is where the column-0 anchor used to live.  Isar is
    whitespace-insensitive, so the anchor answered "is this a command?" with
    "is it flush left?", which is a different question: `Error_Monad_Add`
    indents its whole theory body and had 0 of its 14 declarations recognised,
    while 91 AFP theories reported no entries at all.  Asking the outer view
    instead keeps the protection the anchor was really providing — a `lemma`
    written inside a term or a comment is blanked there, so it cannot match —
    without tying recognition to layout.
    """
    stripped = outer_line.lstrip()
    if not stripped:
        return None, 0
    return _match_decl(stripped, table), len(outer_line) - len(stripped)


# A decl keyword may stand alone on its line with the name on a *following*
# line (~1,866 AFP entries):
#     inductive_set
#       myset :: "nat set"
#     definition
#       foo :: "nat" where "foo = 0"
# Bound the forward scan to a few lines so a truncated/malformed file cannot
# run on looking for a name that is not there.  Counted over blank and `text`
# lines only: a formal comment is one lexer token however far it wraps, so it
# is skipped without charge — see `_lookahead_name` [comment-before-name].
_NAME_LOOKAHEAD_LINES = 3
# Absolute cap on the walk, so "skipped without charge" still cannot run away
# on a file whose comment never closes.  Generous against real source: the
# longest pre-name comment measured over the AFP and the distribution is 4
# lines (`HOL/UNITY/WFair.thy:37`).
_NAME_SCAN_LINES = 40


def _lookahead_name(lines: list[str], start: int, table: dict[str, str],
                    parse_fn, outer: list[str] | None = None,
                    live: list[str] | None = None) -> str:
    r"""The name for a decl whose keyword stood alone: scan forward from the
    0-indexed line ``start``, skipping blank / formal-comment / ``text`` lines,
    and parse the name from the **first content line** with ``parse_fn``.

    Only the first content line is consulted: a continuation name always sits
    immediately after the keyword.  If that line is an anonymous quoted
    statement (``definition "lhs = ..."``) ``parse_fn`` rightly yields ``'?'``
    — the decl really is anonymous, and scanning on would invent a name from
    unrelated following prose.  A following *top-level command* likewise means
    no name here.  Does NOT consume lines — the caller's body scan still covers
    the peeked line, so the body buffer, ``decl_end_line`` and spans are
    exactly as before; only the name changes.

    ``live`` is the tokenizer's redacted view, and asking it is what makes a
    MULTI-LINE formal comment work [comment-before-name].  Testing the raw text
    for a leading ``\<comment>`` recognises only the comment's FIRST line, so a
    comment that wraps left its continuation looking like content and the name
    was read out of the prose: ``HOL/UNITY/WFair.thy:35`` indexed ``is``, out of
    "the rest **is** generic to all forms of fairness", and never indexed
    ``transient`` at all.  It also caught only one of the four spellings, so a
    ``\<^marker>`` on its own line — which `HOL/Analysis` writes on hundreds of
    declarations — yielded ``?``.  The tokenizer already knows both: every such
    line is blank in ``live``.

    A redacted line does not spend the lookahead budget.  That bound exists so
    "a truncated/malformed file cannot run on looking for a name that is not
    there", and a formal comment is ONE token to Isabelle's lexer however many
    lines it spans — its own cartouche already bounds it, so charging the
    budget per line would make the guard fire on well-formed source.  Real
    blank lines and ``text`` blocks still spend it, and ``_NAME_SCAN_LINES``
    caps the walk outright so the runaway the guard was written for stays
    impossible."""
    limit = min(len(lines), start + _NAME_SCAN_LINES)
    budget = _NAME_LOOKAHEAD_LINES
    j = start
    while j < limit and budget > 0:
        stripped = lines[j].strip()
        # Blank in `live` but not in the source == the tokenizer redacted it:
        # a formal comment of any of the four spellings, or one of its
        # continuation lines.  A genuinely empty line is not "redacted".
        redacted = bool(stripped) and live is not None and not live[j].strip()
        if not stripped or redacted or stripped.startswith("\\<comment>") \
                or TEXT_OPEN_RE.match(lines[j]):
            if not redacted:
                budget -= 1
            j += 1
            continue
        probe = outer[j] if outer is not None else lines[j]
        if _match_decl_at(probe, table)[0]:  # next command — no name here
            return "?"
        return parse_fn(stripped)            # first content line is the name
    return "?"


def _heading_at(lines: list[str], i: int,
                prose: bytearray | None = None) -> tuple[str, str, str, int] | None:
    r"""Is line ``i`` (0-indexed) a heading command?  ``(level, opener, rest,
    offset)`` if so, where ``offset`` is 0 or — for the split form — 1, the
    distance to the line the *title* opens on.

    The single answer to "is this a heading", shared by the outline view and the
    prose mask so the two cannot drift apart again.

    ``prose`` is a `_line_mask` of the lines that are already known to be
    document-block bodies or ML — where a *command* cannot start, so a heading
    keyword there is only a word.  Without it, an English sentence inside a
    `text` block is enough:

        text \<open>
          The proof follows Kleinberg & Tardos: "Algorithm Design",
          chapter "Dynamic Programming" \<^cite>\<open>"Kleinberg-Tardos"\<close>
        \<close>

    which `outline` duly reported as a chapter (Monad_Memo_DP, twice in the
    AFP).  That one is harmless past the false entry — it sits inside a block
    that is masked anyway — but the same line with an *odd* number of quotes
    would send `_find_quoted_close` hunting past the end of the block and mask
    live code with it.  Callers that have the spans should always pass them.
    """
    if prose is not None and prose[i + 1]:
        return None
    m = _HEADING_LEAD_RE.match(lines[i])
    if m is None:
        return None
    # A document marker may sit between the command and its title —
    # `subsection\<^marker>\<open>tag unimportant\<close> \<open>Norm\<close>`,
    # 246 of them in HOL/Analysis.  Skipped here rather than read off the outer
    # view, because a heading's TITLE is a cartouche: the view that blanks the
    # marker blanks the title with it, so this one has to read the raw line.
    rest = _skip_formal_comments(lines[i][m.end():])
    here = _TITLE_OPEN_RE.match(rest)
    if here:
        return m.group(1), here.group(1), here.group(2), 0
    # The split form: the command alone on its line, its title on the next —
    # the same shape `_TEXT_BARE_RE` handles for document blocks.  Only ever a
    # one-line lookahead, so a bare word cannot reach an unrelated title.
    if not rest and i + 1 < len(lines):
        nxt = _TITLE_OPEN_RE.match(lines[i + 1])
        if nxt:
            return m.group(1), nxt.group(1), nxt.group(2), 1
    return None


def extract_sections(lines: list[str],
                     prose: Iterable[tuple[int, int]] = ()
                     ) -> list[tuple[str, str, int]]:
    """``(level, title, line)`` for every heading — what `outline` prints, and
    the boundary lines `compute_spans` breaks entries on.

    The title is read to the end of its own line when it wraps, as it always
    was: an outline is a one-line-per-heading index, not a transcript.

    ``prose`` is the already-known document-block / ML spans — see
    `_heading_at`.  Omitting it means an unguarded scan.
    """
    mask = _line_mask(len(lines), prose) if prose else None
    out: list[tuple[str, str, int]] = []
    for i in range(len(lines)):
        found = _heading_at(lines, i, mask)
        if found is None:
            continue
        level, opener, rest, _at = found
        close_idx = rest.find(_TITLE_CLOSE[opener])
        title = rest[:close_idx] if close_idx >= 0 else rest
        out.append((level, title.strip(), i + 1))
    return out


def _find_balanced_close(lines: list[str], start: int) -> int:
    """Given a 0-indexed start line that opens a cartouche block, return the
    0-indexed line of the matching close (counts open/close balance).
    Returns start if no balance found (malformed).

    Both spellings count, `\\<open>`/`\\<close>` and `‹`/`›`, as `_CART_OPEN`
    and `_CART_CLOSE` list them.  Counting only the ASCII spelling meant a
    multi-line `‹...›` body scored depth 0 on its first line and was reported as
    a one-line block, leaving the rest of it live.
    """
    depth = 0
    for i in range(start, len(lines)):
        depth += sum(lines[i].count(tok) for tok in _CART_OPEN)
        depth -= sum(lines[i].count(tok) for tok in _CART_CLOSE)
        if depth <= 0 and i >= start:
            return i
    return start


def _find_quoted_close(lines: list[str], start: int) -> int:
    r"""Given a 0-indexed line that opens a `"..."` title, return the 0-indexed
    line of its closing quote.  Returns `start` if there is none (malformed),
    matching `_find_balanced_close`.

    Counting, not balancing: quoted strings do not nest, so the title ends at
    the next unescaped `"` wherever it falls — which is Isabelle's own lexing
    rule, and the reason the scan is not bounded by a line budget.  Nearly
    always the same line (3,978 of 3,980 in the AFP); the two that wrap are
    exactly the residue a "rare enough to ignore" call would leave live.
    """
    if len(_UNESCAPED_QUOTE_RE.findall(lines[start])) >= 2:
        return start
    for i in range(start + 1, len(lines)):
        if _UNESCAPED_QUOTE_RE.search(lines[i]):
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
                          opens: Callable[[list[str], int], int | None]
                          ) -> list[tuple[int, int]]:
    r"""Return [(start, end)] (1-indexed inclusive) for each balanced cartouche
    block that ``opens`` reports at some line, skipping past each block found.
    Shared by `extract_text_blocks` (document commands) and
    `extract_comment_ranges` (``\<comment>`` bodies), which differ only in that
    predicate.

    ``opens(lines, i)`` returns ``None`` if no block starts at line ``i``, and
    otherwise the **offset from ``i`` at which the cartouche itself opens** —
    ``0`` in the usual case, ``1`` for a command word whose cartouche is on the
    next line.  It takes the whole list rather than one line because that
    lookahead cannot be decided from the opening line alone, and the offset is
    returned rather than assumed because the two callers must not share it:
    balancing from the wrong line would let a bodyless ``\<comment>`` swallow
    the next unrelated cartouche.  The block *span* still starts at ``i``, so a
    split opener's command word is inside its own block.
    """
    out: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        at = opens(lines, i)
        if at is None:
            i += 1
            continue
        end = _find_balanced_close(lines, i + at)
        out.append((i + 1, end + 1))
        i = end + 1
    return out


def extract_text_blocks(lines: list[str]) -> list[tuple[int, int]]:
    """Return [(start_line, end_line)] (1-indexed inclusive) for the document
    blocks `text \\<open>...\\<close>`, `text_raw` and the in-proof `txt`.  Body
    is not stored — callers slice from sec.source() when needed.

    This is the *only* place prose blocks are recognised, which is why a command
    missing from `TEXT_OPEN_RE` leaks so widely: the result feeds the
    declaration mask, `graph._noise_spans` (so citation and step scanners skip
    it), the `--with-comments` prose view, and per-entry preambles.

    A **split opener** counts: the command word alone on its line with the
    cartouche on the next one is the same command, written over two lines.

        text
          \\<open>We have developed two points of view on freeness:
        \\<^item> being generated by a code.
        \\<close>

    Only the immediately following line is consulted, and it must open a
    cartouche — otherwise a bare `text` would reach forward to the next
    unrelated one.  76 blocks in the AFP (282 live prose lines), whose English
    was being mined for both citations and proof methods.
    """
    def opens(ls: list[str], i: int) -> int | None:
        if TEXT_OPEN_RE.match(ls[i]):
            return 0
        if _TEXT_BARE_RE.match(ls[i]) and i + 1 < len(ls) \
                and any(tok in ls[i + 1] for tok in _CART_OPEN):
            return 1
        return None

    return _scan_balanced_blocks(lines, opens)


def extract_heading_spans(lines: list[str],
                          prose: Iterable[tuple[int, int]] = ()
                          ) -> list[tuple[int, int]]:
    r"""Return [(start_line, end_line)] (1-indexed inclusive) for every heading.

    A heading is prose, but it was in no prose list, so its English was scanned
    as Isar.  40,726 headings in the AFP — two orders of magnitude more than the
    `txt` blocks of [txt-prose], and mostly *one-line* headings, which is why
    looking only at the ones that wrap understates it.  What that cost was not
    mainly method tokens but citations: a `section \<open>Consequences proved
    using helper\<close>` parses "using helper" as a fact list and edges the
    enclosing scope to `helper`, so a lemma named only in a heading looks used
    and drops out of `unused`.

    Recognition is `_heading_at`, shared with `extract_sections` — one answer to
    "is this a heading", so the mask and the `outline` view cannot disagree
    about it again.  Three closers, because the openers differ: a cartouche
    balances (and so carries a wrapped heading's continuation lines with it),
    while a quoted title counts to its closing quote.

    ``prose`` is the already-known document-block / ML spans — see `_heading_at`.
    """
    mask = _line_mask(len(lines), prose) if prose else None
    out: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        found = _heading_at(lines, i, mask)
        if found is None:
            i += 1
            continue
        _level, opener, _rest, at = found
        close = (_find_quoted_close if opener == '"' else _find_balanced_close)
        end = close(lines, i + at)
        out.append((i + 1, end + 1))
        i = end + 1
    return out


def extract_comment_ranges(lines: list[str]) -> list[tuple[int, int]]:
    """Return [(start_line, end_line)] (1-indexed inclusive) for every
    \\<comment> \\<open>...\\<close> annotation, including multi-line bodies.

    Tracks \\<open>/\\<close> balance starting from the line that contains
    \\<comment>.  A \\<comment> on a line without \\<open> yields a single-
    line range (covers tag-only annotations without explicit body) — hence
    offset 0 always, never the lookahead `extract_text_blocks` uses: a bodyless
    note must not annex the next cartouche in the file.
    """
    return _scan_balanced_blocks(
        lines, lambda ls, i: 0 if _MARGINAL in ls[i] else None)


# Outer-syntax regions that are not Isar proof text, and the commands that
# introduce them.  These are LEXICAL: the isar-ref manual specifies them
# completely and a user cannot extend them (unlike the command grammar, which
# `scan_keywords` reads from each theory header).  A name mentioned inside one
# is not a fact citation, and a command word inside one is not a command.
_CART_OPEN = ("\\<open>", "‹")
_CART_CLOSE = ("\\<close>", "›")
# Markers that OWN the cartouche following them, so its body is prose, deleted
# text, raw LaTeX or a document tag rather than live Isar — as opposed to a
# bare cartouche, whose owner is the command in front of it and which is
# usually a term.  Isabelle's four formal comments exactly; see
# `FORMAL_COMMENTS`, where they are named, and which the name grammar reads
# from the same tuple so the two views cannot disagree about what a marker is.
_REDACTING_MARKERS = FORMAL_COMMENTS
# Commands whose body is an ML cartouche.  ML source has its own namespace, so
# an identifier there never cites an Isabelle fact.
_ML_BODY_COMMANDS = frozenset({
    "ML", "ML_prf", "ML_val", "ML_command", "ML_export",
    "setup", "local_setup", "declaration", "syntax_declaration",
    "attribute_setup", "method_setup", "simproc_setup", "oracle",
    "parse_translation", "print_translation", "typed_print_translation",
    "parse_ast_translation", "print_ast_translation",
})
# ML brought in by path rather than by cartouche: no body to redact, but still
# a command, so it ends the span above it (`_SPAN_BOUNDARY_COMMANDS`).  Kept
# out of `_ML_BODY_COMMANDS` so it never arms a cartouche it does not own.
_ML_FILE_COMMANDS = frozenset({
    "ML_file", "ML_file_debug", "ML_file_no_debug",
    "SML_file", "SML_export", "SML_import",
})
_LEADING_TOKEN_RE = re.compile(r"^\s*([A-Za-z][A-Za-z_0-9']*)")
# States in which the characters being scanned are not live Isar text.  Note
# `term` (a live cartouche) is deliberately absent: it is tracked, not redacted.
_NOISE_STATES = frozenset({"comment", "verbatim", "cartouche"})

# One compiled alternation per state, giving the next position that can change
# it.  The scan jumps region to region rather than stepping character by
# character: it runs over every theory on every invocation, so the constant
# factor is the difference between a free check and a visible one.
_MARKER_ALT = "|".join(re.escape(s) for s in _REDACTING_MARKERS)
_MARKER_OPEN_RE = rf'(?:{_MARKER_ALT})\s*(?:\\<open>|‹)'
# Every token that can change the state, in ONE alternation, so a line costs a
# single pass of the regex engine and Python-level work only per token found.
# Order matters: `\\` and `\"` precede `"` so an escaped quote inside a string
# is consumed rather than read as the closing delimiter, and the marker forms
# (which swallow their cartouche) precede the bare `\<open>`.
#
# `\\` carries `(?!<)` because ordered choice would otherwise let the escape
# eat half a markup symbol.  Isabelle reads source in two passes — a SYMBOL
# layer where `\<close>` is one atom, then a token layer where `\\` is a string
# escape — so in `\<open>\\<close>` (the residuation operator: a cartouche whose
# body is one backslash) the close is a symbol and not two escaped characters.
# Scanning both layers at once let the escape consume the body backslash plus
# the `\` of `\<close>`, leaving the scanner in cartouche state to the end of
# the file.  The lookahead declines the escape exactly when the second
# backslash begins a markup token, which is symbol-precedence expressed here.
_SCAN_RE = re.compile(
    r'\(\*|\*\)|\{\*|\*\}|\\\\(?!<)|\\"|"|'
    + _MARKER_OPEN_RE + r'|\\<open>|‹|\\<close>|›')
# Nothing to redact unless one of these appears somewhere in the theory.  Most
# of the cost is skipped outright on a file with no comment and no ML.  Built
# from `_REDACTING_MARKERS`, not respelled: a marker this gate does not know
# about takes the early return and is never tokenised at all, which is silent.
_ANY_REGION_RE = re.compile(r'\(\*|\{\*|' + _MARKER_ALT)


def _leads_with_ml(line: str) -> bool:
    """True if `line` opens with a command whose body is an ML cartouche."""
    m = _LEADING_TOKEN_RE.match(line)
    return m is not None and m.group(1) in _ML_BODY_COMMANDS


def _opens_ml_body(lines: list[str], i: int, pos: int) -> bool:
    r"""Is the cartouche at ``lines[i][pos]`` an ML command's body?

    Asked only where a cartouche actually opens, rather than tested on every
    line: the command keyword is what separates an ML body from a term, and
    cartouche openings are a few thousand per corpus where lines are millions.

    True when the command is on the same line (``ML \<open>``, ``method_setup
    foo = \<open>``), or when the cartouche starts its own line and the nearest
    preceding non-blank line is the command (a body written under its keyword).
    """
    line = lines[i]
    if _leads_with_ml(line):
        return True
    if line[:pos].strip():
        return False  # something else on this line owns the cartouche
    k = i - 1
    while k >= 0 and not lines[k].strip():
        k -= 1
    return k >= 0 and _leads_with_ml(lines[k])


def _scan_nonisar_spans(
        lines: list[str], want_inner: bool = True,
) -> tuple[list[list[tuple[int, int]]], dict[int, set[int]],
           list[list[tuple[int, int]]]]:
    r"""Per-line ``[(start_col, end_col)]`` half-open character spans that are
    NOT live Isar text: ``(* ... *)`` comments (which nest), legacy ``{* ... *}``
    verbatim, ``\<^cancel>\<open>...\<close>`` regions, ``\<comment>
    \<open>...\<close>`` marginal notes, and ML command bodies.

    A character-level state machine, because none of this is a regular language:
    comments nest, so the end needs a depth counter (a non-greedy match to the
    first ``*)`` stops early), and a ``(*`` inside a ``"..."`` term does not open
    a comment at all, so string context must be tracked.

    ``"..."`` regions are tracked but NEVER reported: a double-quoted region
    holds an inner-syntax term, so the `mono` in ``lemma "mono f"`` is a real
    citation that the call graph must keep.  Likewise a bare cartouche is left
    live — only the cartouche of an ML command is a body, and the command
    keyword decides that, exactly as `TEXT_OPEN_RE` decides it for `text`.
    """
    spans: list[list[tuple[int, int]]] = [[] for _ in lines]
    # Columns at which a GENUINE `\<comment>` note opens, per 1-indexed line.
    # The scan is the only thing that can tell those apart from a `\<comment>`
    # written inside a `(* ... *)` block or an ML body: the latter is never
    # tokenised as a marker at all, because the machine is in `comment` /
    # `cartouche` state when it goes past.  `_attach_annotations` needs exactly
    # this distinction — a note annotating commented-out text annotates
    # nothing, and must not be charged to the proof the region sits in.
    notes: dict[int, set[int]] = {}
    # Per-line spans that are NOT outer syntax — the noise above PLUS the
    # `"..."` terms and live cartouches the noise scan deliberately keeps.
    # `state == "text"` is precisely Isar's command position, so the complement
    # of these spans is where a command keyword can legitimately appear.  The
    # machine already knows this; it just never said so.
    inner: list[list[tuple[int, int]]] = [[] for _ in lines] if want_inner else []
    inner_start = -1
    # Per line: was the scanner mid-region when the line began?  A term, string
    # or comment carries across newlines, so this is the one thing the spans
    # cannot say — a wholly-inside-a-term line and a wholly-blank line both
    # have empty outer content, and only this tells them apart.
    open_at = bytearray(len(lines))
    state = "text"
    depth = 0    # nesting depth: comment `(*`, or cartouche `\<open>`
    start = -1   # column where the current noise region began on this line
    resume = "text"   # state to return to when the current marker cartouche ends
    resume_depth = 0  # ...and the nesting depth that state was at
    for i, line in enumerate(lines):
        n = len(line)
        if state in _NOISE_STATES:
            start = 0  # region continues from the previous line
        if want_inner:
            inner_start = -1 if state == "text" else 0
            open_at[i] = state != "text"
        for m in _SCAN_RE.finditer(line):
            tok, pos = m.group(), m.start()
            was_text = state == "text"
            if state == "text":
                if tok == "(*":
                    state, depth, start = "comment", 1, pos
                elif tok == "{*":
                    state, start = "verbatim", pos
                elif tok == '"':
                    state = "string"
                elif tok.startswith(_REDACTING_MARKERS):
                    # `\<^cancel>` (deleted text) or `\<comment>` (a marginal
                    # note) plus the cartouche it owns — matched as one token.
                    state, depth, start = "cartouche", 1, pos
                    if tok.startswith(_MARGINAL):
                        notes.setdefault(i + 1, set()).add(pos)
                elif tok in _CART_OPEN:
                    if _opens_ml_body(lines, i, pos):  # ML body: redact it
                        state, depth, start = "cartouche", 1, pos
                    else:  # a term / prose cartouche: one token, but kept live
                        state, depth = "term", 1
                # a stray `*)` / `*}` / `\<close>` in text is not a delimiter
            elif state == "string":
                if tok == '"':          # `\"` and `\\` consume themselves
                    state = "text"
                elif tok.startswith(_REDACTING_MARKERS):
                    # Isabelle's INNER syntax takes cartouche comments too, so
                    # a `\<comment> \<open>round 1\<close>` sitting inside a
                    # multi-line `"..."` term is prose, not part of the term.
                    # It resumes the string afterwards rather than dropping to
                    # `text`, or the rest of the term would be read as outer
                    # syntax — which is how a `(*` in the term below it would
                    # open a comment that swallows the proof.
                    state, resume, resume_depth = "cartouche", "string", depth
                    depth, start = 1, pos
                    if tok.startswith(_MARGINAL):
                        notes.setdefault(i + 1, set()).add(pos)
            elif state == "comment":
                if tok == "(*":
                    depth += 1
                elif tok == "*)":
                    depth -= 1
                    if depth <= 0:
                        spans[i].append((start, m.end()))
                        state, start = "text", -1
            elif state == "verbatim":
                if tok == "*}":         # legacy verbatim does not nest
                    spans[i].append((start, m.end()))
                    state, start = "text", -1
            elif state == "term":
                # A live cartouche (a term, or `text` prose).  Isabelle scans a
                # cartouche as ONE token, so a `(*` inside it — the operator
                # section in `\<open>fold (*) xs\<close>` is the everyday case —
                # opens no comment.  Tracked only to skip past it; never redacted.
                #
                # `endswith`, not membership: a nested `\<comment>\<open>` is
                # matched as ONE token that ENDS in an opener, and testing
                # membership would miss the nesting while still counting its
                # `\<close>` — closing the enclosing cartouche a level early and
                # letting the rest of its body back into live text.
                if tok.startswith(_REDACTING_MARKERS):
                    # A note inside a cartouche TERM — the same inner-syntax
                    # case as inside `"..."`, and the commoner one, since a
                    # `definition foo :: \<open>...\<close> where \<open>...`
                    # body is annotated line by line.  The enclosing term's own
                    # nesting depth is stashed and restored, or resuming it
                    # would resume at the note's depth.
                    state, resume, resume_depth = "cartouche", "term", depth
                    depth, start = 1, pos
                    if tok.startswith(_MARGINAL):
                        notes.setdefault(i + 1, set()).add(pos)
                elif tok.endswith(_CART_OPEN):
                    depth += 1
                elif tok in _CART_CLOSE:
                    depth -= 1
                    if depth <= 0:
                        state = "text"
            else:  # cartouche body (ML, a marginal note, or cancelled text)
                if tok.endswith(_CART_OPEN):
                    depth += 1
                elif tok in _CART_CLOSE:
                    depth -= 1
                    if depth <= 0:
                        spans[i].append((start, m.end()))
                        state, start = resume, -1
                        depth, resume, resume_depth = resume_depth, "text", 0
            # The outer-syntax boundary, maintained in ONE place rather than a
            # line in each of the eight arms above that can cross it — the arms
            # are where this scanner has historically drifted, and a rule
            # stated once cannot disagree with itself.
            if not want_inner:
                continue
            if was_text and state != "text":
                inner_start = pos
            elif not was_text and state == "text":
                inner[i].append((inner_start, m.end()))
                inner_start = -1
        if state in _NOISE_STATES and 0 <= start < n:
            spans[i].append((start, n))
        if want_inner and state != "text" and 0 <= inner_start < n:
            inner[i].append((inner_start, n))
        # Every state persists to the next line.  A ``"..."`` term routinely
        # spans lines, and dropping string state at the newline is not a small
        # error: the continuation line of a multi-line term is where `map2 (*)`
        # sits, and reading that operator section as a comment opener silently
        # swallows the rest of the proof.  (Being wrong in this direction only
        # ever leaves noise unrecognised; being wrong in the other deletes live
        # source, so an unbalanced quote costs missed comments, nothing more.)
    return spans, notes, inner, open_at


def scan_regions(lines: list[str], want_inner: bool = False,
                 ) -> tuple[dict[int, list[tuple[int, int]]],
                            dict[int, set[int]],
                            dict[int, list[tuple[int, int]]],
                            bytearray]:
    r"""One tokenizer pass, all four of its outputs.

    Returns ``(spans, note_starts, inner_spans, open_at)``:

    * ``spans`` — ``{line_no: [(lo, hi)]}``, the non-Isar character spans;
    * ``note_starts`` — ``{line_no: {col}}``, where a genuine ``\<comment>``
      note opens.  A ``\<comment>`` written *inside* a ``(* ... *)`` block or
      an ML body is absent, because the scanner never reaches it in a live
      state — which is the distinction `extract_comment_lines` cannot make from
      the text alone, since the two are spelled identically.
    * ``inner_spans`` — ``{line_no: [(lo, hi)]}``, everything that is NOT outer
      syntax: the noise above, plus ``"..."`` terms and live cartouches.  Its
      complement is command position, which is what the declaration grammar
      wants to know and has been approximating with a column-0 anchor.  Empty
      unless ``want_inner``.
    * ``open_at`` — 0-indexed by line, 1 where the line BEGAN inside a region
      (a term, string or comment carried over the newline).  The spans cannot
      say this: a line wholly inside a term and a wholly blank line both have
      empty outer content.  Telling them apart is what replaces the quote-parity
      counting the statement scans used to do by hand.  Zeroed unless
      ``want_inner``.

    ``want_inner`` is a flag rather than always-on because the two outputs have
    very different densities: noise is rare, inner syntax is on 49% of all
    lines, so recording it costs +18% of the scan (+5.8% of a whole parse,
    `scripts/probe_fastpath.py`).  Worth paying where command position is
    wanted, not worth paying to answer "where are the comments".

    It also disables the early return, which is only sound for the noise
    outputs: every theory has terms, so a theory taking that path would report
    "no inner syntax" and hand its ``"..."`` back as command position — exactly
    the false positive the anchor exists to prevent.  (The early return earns
    little regardless: 7% of theories, 2.7% of lines, and its own gate scans
    every line twice to decide.)
    """
    if not want_inner and not any(_ANY_REGION_RE.search(ln) for ln in lines) \
            and not any(_leads_with_ml(ln) for ln in lines):
        return {}, {}, {}, bytearray(len(lines))
    spans, notes, inner, open_at = _scan_nonisar_spans(lines, want_inner)
    return ({i: sp for i, sp in enumerate(spans, 1) if sp},
            notes,
            {i: sp for i, sp in enumerate(inner, 1) if sp},
            open_at)


def extract_nonisar_spans(lines: list[str]) -> dict[int, list[tuple[int, int]]]:
    r"""Return ``{line_no: [(start_col, end_col)]}`` — the non-Isar character
    spans of each line that has any, 1-indexed by line and half-open by column.

    Sparse on purpose: most lines carry no region at all, and the map is held
    for the lifetime of the `TheorySection`, so an entry per line would cost
    more memory than the source itself.  An empty result means the theory has
    nothing to redact, which `TheorySection.live_source` uses to hand back the
    original list rather than a copy.

    The span half of :func:`scan_regions`.  :func:`extract_nonisar_ranges`
    narrows it to whole lines; the column detail is what
    :meth:`model.TheorySection.live_source` needs, so a comment trailing live
    proof text can be blanked without taking the proof text with it.
    """
    return scan_regions(lines)[0]


def extract_nonisar_ranges(
        lines: list[str],
        spans: dict[int, list[tuple[int, int]]] | None = None,
        ) -> list[tuple[int, int]]:
    r"""Return ``[(start_line, end_line)]`` (1-indexed inclusive) for lines that
    hold no live Isar text — every non-blank character lies inside a comment,
    a ``\<^cancel>`` region, legacy verbatim, or an ML body.

    Deliberately conservative: a line with live code *outside* such a region
    (``by simp (* see foo *)``) is NOT reported.  These ranges drive
    line-granular consumers (`_noise_spans`, the span-boundary mask), and
    reporting that line to them would blank its live half and drop a real
    citation — a false negative, worse than the false positive it would cure
    and harder to notice.  The scanners get the columns instead, via
    :meth:`model.TheorySection.live_source`.

    ``spans`` accepts an :func:`extract_nonisar_spans` result already computed
    by the caller, so `_parse_one` tokenises each theory once rather than twice.
    """
    if spans is None:
        spans = extract_nonisar_spans(lines)
    # Only the lines the tokenizer touched can qualify, and they are a few
    # per cent of the file — walking the sparse map is a scan of those, not of
    # every line in the theory.
    marked: list[int] = []
    for i in sorted(spans):
        line = lines[i - 1]
        live, prev = [], 0
        for a, b in spans[i]:
            live.append(line[prev:a])
            prev = max(prev, b)
        live.append(line[prev:])
        if not "".join(live).strip():
            marked.append(i)
    out: list[tuple[int, int]] = []
    for ln in marked:
        # Extend across an intervening blank run as well as directly: a blank
        # line inside an ML body carries no citation and no command either way,
        # and coalescing keeps the range list short (the membership tests in
        # `grep` are linear in it).
        if out and all(not lines[k - 1].strip()
                       for k in range(out[-1][1] + 1, ln)):
            out[-1] = (out[-1][0], ln)
        else:
            out.append((ln, ln))
    return out


_CART_TOKEN_RE = re.compile(r"\\<open>|‹|\\<close>|›")


def _cartouche_body(rest: str) -> str:
    r"""`rest` up to the `\<close>` matching the cartouche already open.

    Cartouches NEST, and a marginal note nests one more often than not: an
    assumption gloss names the term it is about, and naming a term means
    quoting it.  `Lifschitz_Consistency:102`::

        \<comment> \<open>For a sound system \<open>\<Sigma>\<close>\<close>

    Cutting at the first `\<close>` stops after `\<open>\<Sigma>`, which loses
    the end of the sentence and leaves an unbalanced cartouche in the output.
    6,014 of the AFP's 21,683 notes (27.7%) nest, so this is the common case
    rather than a corner: they concentrate in exactly the statement glosses
    that only became visible once annotations were tagged and attached.

    The inner markers are KEPT: `query` prints Isabelle's notation as the
    author wrote it everywhere else (`\<^cite>\<open>...\<close>` in a preamble
    preview), and a note is not the place to start paraphrasing it.
    """
    depth = 1
    for m in _CART_TOKEN_RE.finditer(rest):
        if m.group() in ("\\<open>", "‹"):
            depth += 1
            continue
        depth -= 1
        if depth == 0:
            return rest[:m.start()]
    return rest   # the note runs past this line: take the rest of it


def extract_comment_lines(lines: list[str],
                          notes: dict[int, set[int]] | None = None,
                          ) -> list[tuple[int, str]]:
    r"""Return [(line_no, content)] for `\<comment> \<open>...\<close>`
    annotations.  `content` is the prose inside the cartouche, on the note's
    first line, cut at the `\<close>` that MATCHES its opening (see
    :func:`_cartouche_body`) — or the rest of the line if the note runs on.

    These become `Entry.annotations` — the note is charged BACKWARD, to the
    entry it sits inside, because a marginal note is about the text it follows.

    ``notes`` (the second half of :func:`scan_regions`) filters out a
    ``\<comment>`` that is itself inside a commented-out block or an ML body.
    Text alone cannot tell those apart — they are spelled identically — but the
    scanner can, because it never reads one in a live state.  The distinction
    became load-bearing when commented-out declarations stopped being entries:
    the region is now inside the preceding entry's span, so without this filter
    a note annotating deleted proof text would be reported as a roadmap step of
    a proof that never mentions it.
    """
    out = []
    for i, line in enumerate(lines, 1):
        m = COMMENT_LINE_RE.search(line)
        if not m:
            continue
        if notes is not None and m.start() not in notes.get(i, ()):
            continue
        out.append((i, _cartouche_body(m.group(1)).strip()))
    return out


def extract_entries(lines: list[str],
                    custom: dict[str, str] | None = None,
                    nonisar_ranges: list[tuple[int, int]] | None = None,
                    outer: list[str] | None = None,
                    open_at: bytearray | None = None,
                    live: list[str] | None = None,
                    ) -> list[Entry]:
    r"""Parse `lines` into entries.

    `outer` is the outer-syntax view (`TheorySection.outer_source`), used to
    decide WHERE a command starts; the raw `lines` are used to read what it
    says.  That split is the point: a declaration's name can live inside a term
    (`definition "lift_opt m e \<equiv> ..."`), which `outer` blanks, so
    recognition and extraction genuinely need different views.

    Computed here when not supplied, rather than falling back to a column-0
    anchor — one recognition rule, so a caller that omits it gets the same
    answer more slowly rather than a different answer.

    `live` is the third view (noise blanked, terms kept).  It is needed only for
    a target name written as a quoted identifier, which `outer` blanks, and is
    likewise computed here when a caller omits it.
    """
    entries: list[Entry] = []
    i = 0
    if outer is None:
        _sp, _nt, _inner, open_at = scan_regions(lines, want_inner=True)
        outer = blank_all(lines, _inner)
        if live is None:
            live = blank_all(lines, _sp)
    if open_at is None:
        open_at = bytearray(len(lines))

    # Recognised custom commands: this theory's own header declarations, the
    # active root's scanned union (_CUSTOM_COMMANDS, set by load_index), and an
    # explicit `custom` override (tests).  Empty for a plain theory with no
    # `keywords` clause, in which case _match_decl is just a DECL_RE test.
    table: dict[str, str] = dict(_CUSTOM_COMMANDS)
    table.update(scan_keywords(lines))
    if custom:
        table.update(custom)

    # Lines the declaration grammar must not be applied to, because they are
    # not outer syntax at all:
    #
    #  * prose inside a `text \<open>...\<close>` / `text_raw` cartouche, which
    #    is a single token to Isabelle.  A column-0 line there that happens to
    #    begin with a command name — notably a one-letter command such as
    #    Isabelle_C's `C` — is prose, not a declaration;
    #  * the lexical non-Isar regions.  A commented-out declaration is the
    #    common case and it is not rare: authors supersede a `definition` and
    #    leave the old one in a `(* ... *)`, and ML bodies declare ML functions
    #    with `fun`, which Isabelle spells the same way.  Reading either as a
    #    declaration mints an entry that does not exist — it inflates `summary`
    #    counts, appears in `theory` and `find`, and (once its equally phantom
    #    ML citations went) turns up in `unused` as dead code the user cannot
    #    delete, because it is already deleted.
    #
    # Only *wholly* non-Isar lines are excluded, which is the right granularity
    # here: a declaration is recognised at the start of its line, so a line
    # that opens with live code and merely ends in a comment still declares.
    # (1-indexed; skip[i+1] guards source line i+1.)
    if nonisar_ranges is None:
        nonisar_ranges = extract_nonisar_ranges(lines)
    skip = _line_mask(len(lines),
                      list(extract_text_blocks(lines)) + list(nonisar_ranges))

    while i < len(lines):
        line = lines[i]
        # No line-level mask here: the outer view already blanks comments, ML
        # bodies, cancelled text and `text`-block prose, so a declaration
        # written in any of them cannot match.  Verified by corpus diff — the
        # entry set is identical with the mask removed.  `skip` is still read
        # in the goal route, where it draws a distinction the outer view alone
        # cannot: a line that is wholly PROSE versus one that is wholly TERM.
        md, indent = _match_decl_at(outer[i], table)
        if md is None:
            i += 1
            continue

        keyword, tag, route = md
        # The keyword occupies the same columns in `outer` as in `line` — the
        # views are length-preserving — so the raw text after it starts here.
        line = line[indent:]
        decl_line = i + 1  # 1-indexed source line

        # --- Locale / class heads ---
        if route == "target":
            # The name comes from `_target_opener`, the same reader
            # `_block_stacks` uses to attribute an entry to its enclosing
            # locale.  One parser for one grammar: a name it declines to read
            # (`context fixes x`) is one no entry should carry either.
            opened = _target_opener(
                outer[i], live[i] if live is not None and i < len(live) else None)
            name = (opened[1] if opened and opened[1] else "?")
            rest = line[len(keyword):].strip()
            buf = [f"{tag} {rest}"]
            # The span is the HEAD only — up to but not including `begin`,
            # which `_is_boundary_at` already stops at.  The body's
            # declarations are entries in their own right, so covering it
            # would give `enclosing` two owners for every line inside.
            i, decl_end_line, body = _scan_decl_body(
                lines, outer, live, open_at, table, i + 1, decl_line)
            buf.extend(body)
            entries.append(Entry(tag, name, "\n".join(buf),
                                 thy_line=decl_line,
                                 decl_end_line=decl_end_line,
                                 bindings=_locale_facts(
                                     outer, decl_line, decl_end_line, name)))
            continue

        # --- Simple one-concept declarations ---
        if route == "typedecl":
            rest = line[len(keyword):].strip()
            rest = re.sub(r"\s+where$", "", rest)
            name = _parse_typedecl_name(rest)
            if name == "?" and not _strip_decl_prefix(rest, typevars=True):
                name = _lookahead_name(lines, i + 1, table,
                                       _parse_typedecl_name, outer, live)
            # The body was never read: `decl_end_line` was pinned to the
            # declaration line, so `record state =` at `E_Aodv:16` measured one
            # line against the twenty it spans, and `show` rendered only the
            # `record state =`.  A type declaration ends where any other does.
            buf = [f"{tag} {rest}"]
            i, decl_end_line, body = _scan_decl_body(
                lines, outer, live, open_at, table, i + 1, decl_line, keyword)
            buf.extend(body)
            entries.append(Entry(tag, name, "\n".join(buf),
                                 thy_line=decl_line,
                                 decl_end_line=decl_end_line,
                                 bindings=(
                                     _constructors(outer, decl_line,
                                                   decl_end_line, name)
                                     if tag == "DATATYPE" else
                                     _record_fields(outer, live, decl_line,
                                                    decl_end_line)
                                     if tag == "RECORD" else [])))
            continue

        if route == "axiom":
            # The command's own umbrella entry, ANONYMOUS [axiom-names].  It
            # is load-bearing and must stay: `axiomatization` usually declares
            # its names on the lines BELOW, so without an entry on the command
            # line that line falls to the preceding declaration and `enclosing`
            # names the wrong owner.
            #
            # It used to be named `axiomatization` — a keyword, not a name.
            # `find '^axiomatization$'` answered with 395 of them (374 AFP, 11
            # FOL, 10 ZF): citable names that nothing can cite, and an entry in
            # `summary`'s count for a command rather than a declaration.  `?`
            # is the established spelling for an entry with no name of its own
            # (274 of them in FOL already, from anonymous lemmas), and every
            # place that must skip one already tests for it — the call graph's
            # name set, caller attribution, `unused`, `defs`.
            entries.append(Entry("AXIOM", "?", "AXIOMATIZATION",
                                 thy_line=decl_line, decl_end_line=decl_line))
            # The command line itself may already carry the first name —
            # `axiomatization where process_finite:` or `axiomatization
            # f :: "nat"` — so read its remainder before stepping below it.
            head_names, _ = _axiom_line(outer[i][indent + len(keyword):])
            for head_name in head_names:
                entries.append(
                    Entry("AXIOM", head_name,
                          f"  AXIOM {line[len(keyword):].strip()}",
                          thy_line=decl_line, decl_end_line=decl_line))
            i += 1
            while i < len(lines):
                found, cont = _axiom_line(outer[i])
                if found:
                    for name in found:
                        entries.append(
                            Entry("AXIOM", name,
                                  f"  AXIOM {lines[i].strip()}",
                                  thy_line=i + 1, decl_end_line=i + 1))
                    i += 1
                elif cont:
                    i += 1     # a bare `where` / `and`: same command, go on
                # The command's END is judged on the live line, not the outer
                # one: in the outer view a line that is *all* term blanks to
                # empty, and would be taken for the blank that ends the scan.
                elif lines[i].strip() == "" or TOPLEVEL_RE.match(lines[i]):
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
                name = _lookahead_name(lines, i + 1, table, parse_fn, outer,
                                       live)
            buf = [f"{tag} {rest}"]
            i, decl_end_line, body = _scan_decl_body(
                lines, outer, live, open_at, table, i + 1, decl_line, keyword)
            buf.extend(body)
            entries.append(Entry(tag, name, "\n".join(buf),
                                 thy_line=decl_line,
                                 decl_end_line=decl_end_line,
                                 bindings=[
                                     (s, "sibling") for s in _and_siblings(
                                         outer, decl_line, decl_end_line,
                                         name, tag)
                                 ] + [
                                     (r, "rule") for r in _rule_labels(
                                         outer, decl_line, decl_end_line,
                                         name)]))
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

            # A blank line ends the STATEMENT but not the search for the proof:
            # `lemma foo:` / statement / blank / `proof -` is ordinary Isar, and
            # breaking here left `proof_line` at 0 for 656 AFP facts.  After a
            # blank, any live line that is neither the proof nor a comment ends
            # the search — that is a statement resuming (`shows ...`), and
            # guessing further would risk claiming a later entry's proof.
            saw_blank = False
            while i < len(lines):
                cline = lines[i]
                stripped = cline.strip()
                oline = outer[i]
                inside = open_at[i]
                if BLANK_RE.match(cline):
                    # Only a blank OUTSIDE a term ends the statement: a `do {`
                    # block is routinely written with blank lines between its
                    # steps, and treating those as the end abandoned the search
                    # halfway through the statement.
                    saw_blank = not inside
                    i += 1
                    continue
                if PROOF_RE.match(oline.lstrip()):
                    proof_line = i + 1
                    break
                if _match_decl_at(oline, table)[0] \
                        or (not inside and _is_boundary_at(oline)):
                    break
                if skip[i + 1] and not oline.strip():
                    # Wholly prose — a marginal note or a comment — so not
                    # statement text.  A line that is wholly TERM text has an
                    # empty outer view too, and must still be accumulated, which
                    # is why this asks the noise mask rather than the outer view
                    # alone.
                    #
                    # `Berlekamp_Hensel:64` is the case that broke the parity
                    # counting this replaces: the term's closing quote sits ON
                    # a `\<comment>` line, so the line is not wholly prose, the
                    # note is skipped and the quote is not — and a scan that
                    # skipped the whole line never saw the term close, then
                    # swallowed the following 15 lemmas.
                    i += 1
                    continue
                if saw_blank:
                    # The statement may simply resume — a blank between two
                    # `and c_i:` assumptions is ordinary formatting.  Keep
                    # LOOKING for the proof, but do not resume accumulating:
                    # `decl_end_line` still stops at the blank, so `show
                    # --statement` renders exactly what it rendered before.
                    if inside or _STATEMENT_CONT_RE.match(stripped):
                        i += 1
                        continue
                    break
                if SHOWS_AT_START_RE.match(stripped):
                    in_shows = True
                if in_shows:
                    conjuncts.extend(CONJUNCT_RE.findall(stripped))
                buf.append(f"  {stripped}")
                i += 1
                decl_end_line = i

            # One-liner: `lemma foo: "P" by simp` puts the proof on the same
            # line as the statement, where a scan that starts on the line BELOW
            # the declaration never looks.  It is not always the declaration
            # line — `lemma symcl_converse:` / `"..." by auto` puts it on the
            # statement's continuation — so every line of the statement is
            # checked, earliest first.  1,857 AFP facts, each of which had no
            # proof body at all as far as the drill-down, `shape` and the
            # roadmap were concerned.
            if not proof_line:
                # Whatever is left of the line once inner syntax is blanked IS
                # the outer part, so the proof keyword can simply be searched
                # for.  This replaced a hand-rolled reconstruction of the same
                # idea — strip complete `"..."` pairs, then track whether a
                # leftover quote opened or closed the term to decide which
                # half of the line was proof text — which had to be right about
                # escapes and cartouches, and was not.
                for k in range(decl_line, decl_end_line + 1):
                    if _PROOF_INLINE_RE.search(outer[k - 1]):
                        proof_line = k
                        break

            entries.append(Entry(tag, name, "\n".join(buf),
                                 thy_line=decl_line,
                                 decl_end_line=decl_end_line,
                                 proof_line=proof_line,
                                 bindings=[(c, "conjunct") for c in conjuncts]))
            continue

        i += 1

    # A post-pass rather than threading through five Entry constructions: the
    # block chain is a property of the line an entry starts on, so it can be
    # read off once the entries exist and their start lines are known.
    _attach_targets(entries, outer, live)
    return entries


# Outer commands that declare nothing and so are never indexed as entries, but
# which still bound the declaration above them.  `compute_spans` ends an entry at
# the next entry-or-section line; without these an `instance` proof, a `lemmas`
# alias or the `end` of an enclosing block falls INSIDE the preceding
# declaration's span.  Two things then go wrong: the span reported by
# `enclosing` / `outline` / `largest` is inflated, and a fact cited by the
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
#
# The ML family belongs here for the same reason: an `ML \<open>...\<close>`
# block after a lemma is a command in its own right, so leaving it out let the
# lemma's span run on through the ML body and report it as part of the proof.
_SPAN_BOUNDARY_COMMANDS = frozenset({
    "begin", "end", "instance", "instantiation", "interpretation",
    "sublocale", "locale", "context", "declare", "lemmas", "notation",
    "no_notation", "syntax", "no_syntax", "translations",
    "code_printing", "export_code", "code_datatype", "code_reflect",
    "typedecl", "typedef", "consts", "print_translation",
}) | _ML_BODY_COMMANDS | _ML_FILE_COMMANDS
# Uppercase-initial too: the ML commands (`ML`, `ML_file`, `SML_file`) are
# boundaries, and a lowercase-only anchor would never see them.
_LEADING_CMD_RE = re.compile(r"^([A-Za-z][A-Za-z_0-9]*)")


def _structural_command_lines(
        lines: list[str],
        noise_ranges: list[tuple[int, int]] | None = None,
        outer: list[str] | None = None) -> list[int]:
    """1-indexed lines that open a span-bounding outer command.

    Fed to :func:`compute_spans` alongside the section lines, so a declaration
    ends where the next outer command begins rather than running on through it.
    See ``_SPAN_BOUNDARY_COMMANDS``.

    Matched at command position via ``outer`` — the same rule the declaration
    grammar uses, and for the same reason.  This was anchored at column 0, whose
    stated purpose was that "an indented `end` closing a nested proof does not
    cut anything"; but `end` does not close a proof (`qed` does), and an
    indented `end` closes a nested `context` or `locale`, which is exactly a
    boundary this should report.  The anchor was suppressing real cuts inside
    every indented block.

    Lines in `noise_ranges` are still skipped.  That is now belt-and-braces —
    the outer view already blanks a commented-out command — but it costs
    nothing and the failure it guards against is quiet: a ``(*`` block is
    exactly where a superseded ``end`` sits, and reading one as a real command
    truncates the live declaration above it.
    """
    masked: set[int] = set()
    for start, end in (noise_ranges or []):
        masked.update(range(start, end + 1))
    out: list[int] = []
    for line_no_0, line in enumerate(lines):
        line_no = line_no_0 + 1
        if line_no in masked:
            continue
        probe = (outer[line_no_0] if outer is not None else line).lstrip()
        m = _LEADING_CMD_RE.match(probe)
        if m is None or m.group(1) not in _SPAN_BOUNDARY_COMMANDS:
            continue
        # Report the boundary at the head of any blank run before the command,
        # so the preceding entry's span ends on its last real line rather than
        # on the separating blank — the same "no trailing blanks" rule the
        # entry-to-entry boundary already follows.
        b = line_no
        while b > 1 and not lines[b - 2].strip():
            b -= 1
        out.append(b)
    return out


# --- target blocks (which locale does this declaration belong to?) ---------
#
# Isar makes this unusually cheap.  Every *target* block — `locale`, `class`,
# `context`, `instantiation`, `overloading`, `bundle`, `experiment`, `notepad`,
# and the theory itself — is opened by the token `begin` and closed by `end`,
# whatever command introduced it.  There is no opener→closer table: ONE pair,
# counted at outer-syntax position (100.00% balanced over 1,662 AFP theories,
# max nesting depth 5 — `scripts/probe_block_structure.py`).
#
# A `begin` does not name itself and the opening command may sit several lines
# above it (`locale foo =` / `fixes ...` / `assumes ...` / `begin`), so the rule
# is: remember the most recent target-opening command; the next `begin` consumes
# it.  Overwriting on each opener is what makes a merely-*declared* locale
# (`locale A = fixes x`, never opened) harmless — the next real opener replaces
# it before any `begin` arrives.  Attribution measured at 4,003/4,003
# (`scripts/probe_locale_naming.py`).
#
# A custom block-opener (AutoCorres2's `if_architecture_context`, declared
# `keywords "..." :: thy_decl_block`) needs no special handling here: the push
# happens on the `begin` token regardless of whether the opener was recognised,
# so nesting stays balanced and the block is simply anonymous — which it is.
_BLOCK_TOKEN_RE = re.compile(r"(?<![A-Za-z_0-9'@])(begin|end)(?![A-Za-z_0-9'])")
# `@` joins the left boundary class: auto2 spells its proof closer `@end`,
# which is its own token and not Isar's `end`.

_TARGET_OPEN_RE = re.compile(
    r"^(theory|locale|class|context|instantiation|overloading"
    r"|bundle|open_bundle|experiment|notepad)(?![A-Za-z_0-9'])\s*(.*)$")
# A target's name is spelled like any other Isabelle name — it may open with a
# markup symbol (`locale \<Z> =`, `instantiation \<o> :: ...`) — and may in
# addition be QUALIFIED (`context Rings.dvd begin`, 3 such over 120 AFP
# entries), which an entry name may not.  So this is `SYM_NAME_RE`'s atom plus
# `.`, rather than either regex reused whole: sharing the atom is what keeps
# the two in step, and the dot is the one thing genuinely particular to a
# target.  The quoted spelling (`locale "functor" =`) is handled in
# `_target_name`, as `_name_from` handles it for entries.
_TARGET_NAME_RE = re.compile(rf"(?:{ISA_MARKUP}|[A-Za-z_])(?:{ISA_MARKUP}|[\w'.])*")
# First letters of the opener keywords above — a one-character prefilter:
# bundle, class/context, experiment, instantiation, locale, notepad,
# overloading/open_bundle, theory.
_OPENER_FIRST_CHARS = frozenset("bceilnot")

# Kinds worth reporting as an enclosing target.  `bundle` groups declarations
# but retargets nothing, and `theory` is excluded because every entry is in one.
_TARGET_KINDS = frozenset({"locale", "class", "context", "instantiation"})
# Openers that never carry a name.
_ANON_OPENERS = frozenset({"overloading", "experiment", "notepad"})
# A word here after `context` opens the block or starts an element — it is a
# locale *element*, not the name of an existing locale being reopened.
_NOT_A_TARGET_NAME = frozenset({
    "begin", "fixes", "assumes", "notes", "defines", "includes",
    "constrains", "obtains",
})

# `lemma (in foo) bar: ...` — the target modifier, written on the declaration.
_IN_TARGET_RE = re.compile(r"\(\s*in\s+([A-Za-z_][A-Za-z_0-9'.]*)\s*\)")


def _target_name(rest: str) -> str:
    """The target name at the head of `rest`, or '' if it carries none."""
    mq = QUOTED_NAME_RE.match(rest)
    if mq:
        return mq.group(1)
    mn = _TARGET_NAME_RE.match(rest)
    if not mn or mn.group(0) in _NOT_A_TARGET_NAME:
        return ""
    # A cartouche survives the live view (it is inner syntax, not noise), so
    # reading a name from live must decline `\<open>...` the way `_name_from`
    # does — the symbol alternation would otherwise match it happily.
    if mn.group(0).startswith(RESERVED_NAME_PREFIXES):
        return ""
    return mn.group(0)


def _target_opener(segment: str,
                   live_segment: str | None = None) -> tuple[str, str] | None:
    """`(kind, name)` if `segment` opens a target block, else None.

    `name` is '' for an opener that carries none (`notepad`, `context fixes x`).

    `segment` is the OUTER view, which is what makes this a command position
    rather than a word inside a term.  But outer blanks inner syntax, and a
    target name may be written as a quoted identifier — `locale "functor" =`,
    `instantiation "pseqp" :: ord` — which outer therefore erases.  So when
    `live_segment` is supplied (the same columns in the live view, where terms
    survive), the *name* is read from it while the *keyword* is still matched
    on outer.  That is this module's standing split — outer decides where a
    command starts, a term-keeping view reads what it says — applied to the one
    place that had been reading both from outer.
    """
    stripped = segment.lstrip()
    m = _TARGET_OPEN_RE.match(stripped)
    if not m:
        return None
    kind = m.group(1)
    if kind in _ANON_OPENERS:
        return kind, ""
    rest = m.group(2)
    if live_segment is not None:
        # Anchor on the END OF THE KEYWORD, not on group 2.  The pattern's
        # `\s*` is greedy and outer has blanked the quoted name to spaces, so
        # on `instantiation "pseqp" :: ord` group 2 begins at `::` — past the
        # very columns the name occupies.  Views are length-preserving, so the
        # keyword ends at the same column in both once the left-strip matches.
        rest = live_segment[len(segment) - len(stripped) + m.end(1):].lstrip()
    return kind, _target_name(rest)


def _block_stacks(outer: list[str],
                  live: list[str] | None = None,
                  ) -> list[tuple[tuple[str, str], ...]]:
    """Per line (0-indexed), the chain of enclosing *named target* blocks.

    Openers and `begin`/`end` are read in POSITIONAL order rather than
    line-at-a-time, because `Big_Step_Sterm` writes `context srules begin
    context begin` on one line and a line-granular scan would attribute the
    second block to the first opener.

    The returned tuples are shared between consecutive unchanged lines, so this
    allocates one tuple per block boundary, not one per line.

    `live` is the live view of the same lines, used only to read a *quoted*
    target name that `outer` has blanked; omitting it costs those names and
    nothing else.
    """
    stacks: list[tuple[tuple[str, str], ...]] = []
    stack: list[tuple[str, str]] = []
    cur: tuple[tuple[str, str], ...] = ()
    pending: tuple[str, str] | None = None
    for i, line in enumerate(outer):
        stacks.append(cur)
        lv = live[i] if live is not None and i < len(live) else None
        # Two prefilters, because this runs on every line of every theory.
        # `begin`/`end` appear on ~2 lines per theory, so the token scan is
        # skipped by a substring test; and an opener keyword has one of eight
        # first letters, so most remaining lines skip the alternation too.
        if "begin" in line or "end" in line:
            pos = 0
            for m in _BLOCK_TOKEN_RE.finditer(line):
                op = _target_opener(line[pos:m.start()],
                                    None if lv is None else lv[pos:m.start()])
                if op is not None:
                    pending = op
                pos = m.end()
                if m.group(1) == "begin":
                    stack.append(pending or ("?", ""))
                    pending = None
                elif stack:
                    stack.pop()
            op = _target_opener(line[pos:], None if lv is None else lv[pos:])
            if op is not None:
                pending = op
            cur = tuple(b for b in stack if b[1] and b[0] in _TARGET_KINDS)
            continue
        # The prefilter reads the stripped line; the opener itself is handed
        # the raw one, so its column arithmetic against `live` still lines up.
        if line.lstrip()[:1] in _OPENER_FIRST_CHARS:
            op = _target_opener(line, lv)
            if op is not None:
                pending = op
    return stacks


def _attach_targets(entries: list[Entry], outer: list[str],
                    live: list[str] | None = None) -> None:
    """Record each entry's enclosing named blocks and its `(in foo)` target."""
    stacks = _block_stacks(outer, live)
    for e in entries:
        idx = e.thy_line - 1
        if 0 <= idx < len(stacks):
            e.blocks = stacks[idx]
            mt = _IN_TARGET_RE.search(outer[idx])
            if mt:
                e.in_target = mt.group(1)


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
    entry_starts, starts_keys = _entries_by_line(entries)
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


def _attach_annotations(entries: list[Entry],
                        comment_lines: list[tuple[int, str]]) -> None:
    """Attach each \\<comment> line to its owning entry, tagged by position.

    A note is owned by the entry whose span [thy_line .. thy_end] contains it,
    and tagged by which PART of that entry it sits in — ``decl`` (the
    declaration line), ``statement`` (below the declaration, above the proof),
    or ``proof`` (at or below ``proof_line``).  See ``model._ANNOTATION_KINDS``.
    Runs *after* ``compute_spans``, which is what fixes ``thy_end``.

    Only ``proof`` notes used to be attached.  That is the right rule for a
    *roadmap* and the wrong one for the feature that grew around it: ``show
    --comments-only`` prints preamble + notes with no statement and no proof,
    i.e. it is already the prose view of an entry, and the prose view was
    discarding roughly three quarters of the prose.  Worst of all for a
    ``definition``, which has no proof at all, so no annotation of one could
    ever be shown — and a definition's marginal notes are exactly where its
    construction gets narrated (`Shuffle:54`)::

        ((\\<zeta>a,x',\\<pi>a), a) \\<leftarrow> aby3_do_permute Party1 x;
            \\<comment> \\<open>1st round\\<close>

    Statement notes gloss the specification rather than the derivation
    (`Lifschitz_Consistency:100` annotates every assumption of the theorem),
    which is a genuinely different thing to say about an entry — hence a tag
    and not a flattened list.

    The ``proof`` test is deliberately made BEFORE the ``decl`` one, so the
    ``roadmap`` view this replaces is preserved exactly.  The commonest fact in
    the AFP is a one-liner, ``lemma foo: "P" by simp \\<comment> ...``, whose
    declaration line *is* its proof line; testing ``decl`` first would retag
    every one of those and silently empty the roadmap of the shape that needs
    it most.

    Notes outside every span stay unowned: theory-level prose above the first
    declaration, and the locale-closing ``end \\<comment> \\<open>Context of
    ...\\<close>`` notes, which need locale structure modelled first.  See
    `scripts/probe_roadmap_positions.py` for the distribution.
    """
    # Spans are non-overlapping, so the only candidate is the entry whose
    # thy_line is the greatest <= cline; attach iff cline is within its span.
    # entry_starts is sorted, so the enclosing entry is a bisect away (the old
    # per-comment scan over all entries was O(comments x entries)).
    entry_starts, starts_keys = _entries_by_line(entries)
    for cline, content in comment_lines:
        idx = bisect_right(starts_keys, cline) - 1
        if idx < 0:
            continue          # above the first declaration: theory-level prose
        e = entry_starts[idx][1]
        if cline > e.thy_end:
            continue          # in the gap past the span (locale structure)
        if e.proof_line and cline >= e.proof_line:
            kind = "proof"
        elif cline == e.thy_line:
            kind = "decl"
        else:
            kind = "statement"
        e.annotations.append((cline, content, kind))


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
    # The tokenizer runs FIRST: one pass feeds three consumers — the columns
    # (for `live_source`), the whole-noise lines derived from them (for the
    # line-granular masks), and the declaration scan, which must not read a
    # commented-out `definition` or an ML `fun` as an entry.
    nonisar_spans, note_starts, inner_spans, open_at = scan_regions(
        lines, want_inner=True)
    nonisar_ranges = extract_nonisar_ranges(lines, nonisar_spans)
    outer = blank_all(lines, inner_spans)
    entries = extract_entries(lines, nonisar_ranges=nonisar_ranges,
                              outer=outer, open_at=open_at,
                              live=blank_all(lines, nonisar_spans))
    text_blocks = extract_text_blocks(lines)
    # Document bodies and ML come first because a heading is only a heading
    # when a *command* introduces it: both heading scans take these spans as
    # the places where one cannot start.  See `_heading_at`.
    prose = list(text_blocks) + list(nonisar_ranges)
    outline = extract_sections(lines, prose)
    heading_spans = extract_heading_spans(lines, prose)
    comment_ranges = extract_comment_ranges(lines)
    comment_lines = extract_comment_lines(lines, note_starts)
    # Preambles first: they fix each entry's src_start, which compute_spans
    # uses as the boundary so a leading doc is charged to the entry it
    # documents (not the preceding one).  Roadmaps need the resulting thy_end.
    _attach_preambles(entries, lines, text_blocks)
    compute_spans(entries,
                  [s[2] for s in outline]
                  + _structural_command_lines(
                      lines, comment_ranges + nonisar_ranges, outer),
                  len(lines))
    _attach_annotations(entries, comment_lines)
    for e in entries:
        e.theory = thy
    # Compute body_end_line: for entries with a proof, walk forward from
    # proof_line through proof / by / qed / blank lines, stopping at the
    # next text \<open>...\<close> block or declaration.  For pure
    # declarations (no proof), body ends at decl_end_line.  Computed after
    # compute_spans because _proof_extent needs thy_end as a search bound.
    # Carries `nonisar_ranges` because `_proof_extent` reads them: a boundary
    # written inside a comment is not a boundary, and a section without them
    # would silently answer as if the theory had no comments at all.
    sec_for_extent = TheorySection(thy, thy_path, entries, thy_lines=len(lines),
                                   nonisar_ranges=nonisar_ranges)
    sec_for_extent._source_cache = lines
    for e in entries:
        if e.proof_line:
            e.body_end_line = _proof_extent(sec_for_extent, e.proof_line, e.thy_end)
        else:
            e.body_end_line = e.decl_end_line or e.thy_line
    sec = TheorySection(thy, thy_path, entries, thy_lines=len(lines),
                        outline=outline, text_blocks=text_blocks,
                        heading_spans=heading_spans,
                        comment_ranges=comment_ranges,
                        nonisar_ranges=nonisar_ranges,
                        nonisar_spans=nonisar_spans,
                        inner_spans=inner_spans)
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
                     sections: list[TheorySection],
                     session: str | None = None) -> None:
    """Append a parsed section, deduplicating by resolved absolute path
    so that symlinked theories (e.g.\\ `link/Foo.thy`
    -> `sub/Foo.thy`) appear once even if both the symlink
    and the target are encountered.

    `.thy` paths are parsed with the full Isabelle entry grammar
    (`_parse_one`); any other path is parsed plainly (`_parse_plain`)
    so grep over a Markdown/prose file does not invent bogus entries.

    `session` records the owning Isabelle session (see
    `TheorySection.session`); the first section added for a given path
    wins, so the session tag matches the first ROOT that references the
    theory."""
    if not thy_path.exists():
        return
    resolved = thy_path.resolve()
    if resolved in seen_paths:
        return
    seen_paths.add(resolved)
    if thy_path.suffix == ".thy":
        sec = _parse_one(thy, thy_path)
    else:
        sec = _parse_plain(thy, thy_path)
    sec.session = session
    sections.append(sec)


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
    session_of: dict[Path, str] = {}  # resolved path -> owning session name
    if roots:
        for root_path in roots:
            for session in parse_root_sessions(root_path):
                # In-entry import closure, not just ROOT-declared roots: an AFP
                # entry that declares leaf theories and imports the rest (e.g.
                # AODV declares 1, builds 73) is otherwise silently truncated.
                for name, thy_path in session_theories(session):
                    pairs.append((name, thy_path))
                    # First session that references a theory owns it, matching
                    # the path dedup in `_add_one_section` (first add wins).
                    session_of.setdefault(thy_path.resolve(), session.name)
    else:
        for thy_path in sorted(root_dir.rglob("*.thy")):
            pairs.append((thy_path.stem, thy_path))

    _populate_custom_commands(pairs)
    for name, thy_path in pairs:
        _add_one_section(name, thy_path, seen_paths, sections,
                         session=session_of.get(thy_path.resolve()))


def sections_for_session(session: SessionInfo,
                         seen_paths: set[Path]) -> list[TheorySection]:
    """Parse exactly one session's theories — the unit of work for a batch
    (single-process) corpus run.

    Same three phases as :func:`_sections_from_dir`, scoped to one session:
    reset the custom-command union, pre-scan this session's headers into it,
    then parse.  Resetting matters for equivalence — a batch run must produce
    what the per-invocation runs it replaces produced, and those each saw only
    their own root's keywords.  (Measured: across 992 AFP sessions, 191 distinct
    custom commands and **no** name declared with conflicting kinds, so a
    corpus-wide union would not in fact change any parse today.  The scoping is
    for equivalence and for not depending on that staying true.)

    ``seen_paths`` is the caller's dedup set and must be **shared across
    sessions**, exactly as ``_sections_from_dir`` shares one set across a whole
    root: 47 AFP theory files are referenced by two sessions (``AutoCorres2``
    and ``CParser``), and a per-session set would parse and emit each twice —
    silent duplicate records that inflate every corpus aggregate.  Sharing it
    keeps the same "first session to reference a theory owns it" rule, so the
    session tag on a shared theory matches a whole-root load.
    """
    _CUSTOM_COMMANDS.clear()
    pairs = list(session_theories(session))
    _populate_custom_commands(pairs)
    sections: list[TheorySection] = []
    for name, thy_path in pairs:
        _add_one_section(name, thy_path, seen_paths, sections,
                         session=session.name)
    return sections


def _proof_extent(sec: TheorySection, proof_line: int, thy_end: int) -> int:
    r"""Walk forward from proof_line, return last line that belongs to the proof.
    Stops at `text \<open>...` blocks, section headers, next declarations, or
    end of file.  Returns proof_line itself for one-line proofs.

    A boundary **written inside a comment is not a boundary** — 248 of the
    AFP's 295,775 proofs stopped at one [proof-extent-view]: 231 at a
    commented-out declaration (`ABY3_Protocols/Multiplication_Synthesization:56`),
    11 at a heading inside a `(* ... *)` block, 6 at a commented-out `text`.
    Authors supersede a lemma and leave the old one in a comment, and the proof
    above it was truncated at the `(*`.

    The test is `nonisar_ranges`, the WHOLE-LINE noise mask, and not the outer
    view every other scanner uses.  Two reasons, and both are why this is its
    own change rather than a line in a bigger one: the outer view blanks a
    `text` block's own cartouche, so `startswith("text ")` would stop matching
    there and the boundary would be lost in the other direction; and a
    *partially* commented line (`lemma foo: "P" (* note *)`) is live Isar and
    must still end the proof, which whole-line masking gets right and
    character-level blanking would too but only by accident of what it blanks.

    Two further changes were tried here and are NOT made, because each was
    measured over the AFP and changes **0 records** [proof-extent-anchor]:

    * dropping the column-0 anchor on `DECL_RE` for the deanchored
      `_match_decl_at`.  `thy_end` is already bounded by the declaration
      positions that scan found, so an indented declaration never falls
      strictly inside a proof's span;
    * masking prose inside a ``text`` block.  16 lines there are English
      sentences beginning with a command word — `DiskPaxos_Inv4:66` is
      literally "lemma $action$-$HInv4x$-$q$ proves the other case." — but the
      block's OPENING line already ends the proof, so its body is unreachable
      (`AutoCorres2/TypeStrengthen`: `body_end` 63, block 64..108).

    Only the BOUNDARY tests are masked.  A noise line still advances `last`
    exactly as before, because that is a separate question — whether a trailing
    comment block belongs to the proof — and answering it here would be a
    second change hiding inside this one.
    """
    lines = sec.source()
    noise = _line_mask(len(lines), sec.nonisar_ranges)
    last = proof_line
    for line_no in range(proof_line + 1, thy_end + 1):
        if line_no > len(lines):
            break
        cline = lines[line_no - 1]
        stripped = cline.strip()
        if not noise[line_no]:
            # Stop at top-level documentation blocks (text \<open>...\<close>)
            # but NOT at in-proof Isar annotations (\<comment> \<open>...
            # \<close>), which are routine inside proof bodies.
            if (stripped.startswith("text ")
                    or stripped.startswith("text\\<open>")):
                break
            # `_heading_at`, not a regex of its own: this was a THIRD asker of
            # "is this a heading", and it disagreed — a marked heading and a
            # split heading both ended a proof for `outline` and the prose mask
            # but not here.  7 lines over 2.36M in the AFP, so the size of the
            # disagreement is not the argument; having three recognisers where
            # the comments promise one is.
            if _heading_at(lines, line_no - 1) is not None:
                break
            if DECL_RE.match(cline):
                break
        if stripped:
            last = line_no
    return last
