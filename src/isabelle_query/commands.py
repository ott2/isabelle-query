"""Command implementations — one ``cmd_*`` per subcommand, plus the lookup,
locus, and drill-down helpers they share.

The fifth layer of the DAG (above ``render`` / ``graph``, below ``cli``).  Each
``cmd_*`` takes an already-loaded ``list[TheorySection]`` and prints; it never
loads the index or parses argv (that is ``cli``'s job), so nothing here imports
``cli`` and the layering stays acyclic.  Also home to the pieces used by more
than one command and by the CLI's own routing: theory resolution
(``_resolve_theory`` / ``_suggest_theory``), the shared ``theory:line`` /
``theory:A..B`` locus grammar (``_parse_locus`` / ``_parse_line_range``), and
the proof-block drill-down behind ``enclosing`` (``_proof_blocks`` /
``_enclosing_blocks``).
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from isabelle_query import graph
from isabelle_query._prog import prog_name as _prog_name
from isabelle_layout import parse_thy_imports
from isabelle_query.model import (
    CallGraph,
    CmdFlags,  # noqa: F401  (used in string annotations)
    Entry,
    TheorySection,
    _BINDING_KINDS,
    _CITABLE_TAGS,
    _DEFINITION_TAGS,
)
from isabelle_query.parsing import ISA_SYMBOL, _isa_word_pattern
from isabelle_query.graph import (
    _bfs_depths,
    _build_call_graph,
    _build_def_sites,
    _build_line_index,
    _entry_at_line,
    _entry_by_name,
    _import_depths,
    _leaf_index,
    _noise_ranges,
    _noise_spans,
    _resolve_import,
    _scan_methods,
    _sections_by_theory,
    _shadowed_uses_on_line,
)
from isabelle_query import graph as _graph
from isabelle_query import sites as _sites
from isabelle_query.render import (
    _emit_matches,
    _format_extent,
    _format_target,
    _format_name_line,
    _statement_text,
    _strip_text_wrapper,
    _truncate_preview,
    file_locus,
    locus_labels,
    render_entry,
    theory_locus,
)


# Exit status for a request that could not be resolved — an unknown theory or
# entry name.  Distinct from 0 (the command ran and the answer is genuinely
# empty) and from `cli._EXIT_BAD_ROOT` 2 (the corpus itself could not be read),
# because those are the distinctions a caller has to make.  Documented in
# `README.md`'s exit-status table.
EXIT_UNRESOLVED = 1


def _fail_subject(what: str) -> None:
    """Report an unresolvable SUBJECT on stderr and exit non-zero.

    `_fail_root`'s rule one level down [unresolved-subject].  "No callees of
    zzz" and "there is no zzz" are different answers, and a caller cannot act
    on the difference if both arrive on stdout with status 0 — `$(query callees
    X -c)` captured a sentence where it expected a number, and `$?` said the
    run succeeded.  Same family as the silent-zero root: an empty success for a
    question that was never asked.

    Note the two kinds of empty this keeps apart.  `find zzz -c` prints `0`,
    because searching for something absent is a real search with a real answer;
    `callees zzz` cannot begin, because there is no entry to have callees.  The
    verbs disagree because the questions do, not because they are inconsistent.
    """
    print(f"{_prog_name()}: {what}", file=sys.stderr)
    sys.exit(EXIT_UNRESOLVED)


def _tag_counts(sec: TheorySection) -> tuple[int, int, int]:
    """(#definitions, #lemmas, #theorems) in a section — the D/L/T columns."""
    d = sum(1 for e in sec.entries if e.tag in _DEFINITION_TAGS)
    lem = sum(1 for e in sec.entries if e.tag == "LEMMA")
    thm = sum(1 for e in sec.entries if e.tag == "THEOREM")
    return d, lem, thm


def cmd_summary(sections: list[TheorySection], *,
                by_session: bool = False,
                verbose: bool = False,
                totals_only: bool = False) -> None:
    """The `summary` command.

    Default: the per-theory overview table (one row per theory).  With
    ``by_session`` (or ``totals_only``), roll the same counts up past the
    theory level — an *aggregate* over every theory and session loaded, so
    the command is useful run against a whole corpus (the AFP), a
    multi-session entry, or a single session, not just one theory at a time.
    """
    if totals_only or by_session:
        _summary_aggregate(sections, verbose=verbose, totals_only=totals_only)
        return
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


def _summary_aggregate(sections: list[TheorySection], *,
                       verbose: bool = False,
                       totals_only: bool = False) -> None:
    """Roll the per-theory counts up to the session / corpus level.

    Groups the loaded theories by their owning session (first-seen order,
    which is ROOT-discovery order) and prints one row per session plus a
    grand-total row — the aggregate the plain per-theory table can't give
    over a multi-session tree.  ``verbose`` expands each session to its
    theories (the `wc-theories.py -v` view, with entry counts added);
    ``totals_only`` prints just the grand-total headline (its terse
    default).

    ``Src`` is the theory's logical line count (``TheorySection.thy_lines``,
    = ``wc -l`` for the newline-terminated files Isabelle emits), summed —
    so a per-session subtotal is directly comparable with a `wc -l` figure
    over the same build-referenced file set.  A theory reached through
    several sessions is counted once, under the first (see
    `TheorySection.session`)."""
    groups: dict[str, list[TheorySection]] = {}
    for sec in sections:
        groups.setdefault(sec.session or "(no session)", []).append(sec)

    tot_thy = len(sections)
    tot_src = sum(s.thy_lines for s in sections)
    tot_entries = sum(len(s.entries) for s in sections)
    tot_d = tot_l = tot_t = 0
    for sec in sections:
        d, lem, thm = _tag_counts(sec)
        tot_d += d
        tot_l += lem
        tot_t += thm

    print("# Corpus summary\n")
    print(f"{tot_entries:,} entries · {tot_src:,} source lines across "
          f"{tot_thy:,} theories in {len(groups):,} sessions  "
          f"(parsed live from .thy files)\n")
    if totals_only:
        return

    print("Per-session aggregate — `Src` is summed `.thy` line counts "
          "(`wc -l`-comparable), `D`/`L`/`T` are definition / lemma / theorem "
          "counts.\n")

    if verbose:
        for name, secs in groups.items():
            g_src = sum(s.thy_lines for s in secs)
            print(f"## {name}  ({len(secs):,} theories, {g_src:,} lines)\n")
            print("| Theory | Src | D | L | T |")
            print("|--------|----:|--:|--:|--:|")
            for sec in secs:
                d, lem, thm = _tag_counts(sec)
                print(f"| {sec.theory} | {sec.thy_lines} | {d} | {lem} | {thm} |")
            print()
        return

    print("| Session | Thy | Src | D | L | T |")
    print("|---------|----:|----:|--:|--:|--:|")
    for name, secs in groups.items():
        g_src = sum(s.thy_lines for s in secs)
        g_d = g_l = g_t = 0
        for sec in secs:
            d, lem, thm = _tag_counts(sec)
            g_d += d
            g_l += lem
            g_t += thm
        print(f"| {name} | {len(secs)} | {g_src} | {g_d} | {g_l} | {g_t} |")
    print(f"| **TOTAL** | {tot_thy} | {tot_src} | "
          f"{tot_d} | {tot_l} | {tot_t} |")


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
        discovered through ``isabelle_layout``'s ROOT-walking routines.

    The two forms are tried in that order rather than chosen between, because
    a discovered theory NAME may itself contain a separator: a ROOT can
    address a theory in a subdirectory by path (``theories "LK/Propositional"``
    — the grammar has no per-theory ``in`` clause), and discovery carries it
    under that spelling.  Branching on ``"/"`` alone made such a name
    unresolvable, so ``summary`` printed a row, ``theory``'s "Known theories"
    listed it, and passing it back gave "not found" — the tool disagreeing
    with its own output, and a hole in the round-trip the locus grammar rests
    on.
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
        # Before the stem fallback: the whole argument may be a path-spelled
        # theory NAME.  Exact-first matters — with a `Propositional` section
        # also present, the stem would otherwise capture `LK/Propositional`.
        for s in sections:
            if s.theory == name:
                return s
        # A LABEL, as `render.theory_labels` emits: the shortest directory
        # qualification that names one theory, matched here as a suffix — the
        # exact inverse of how it was built [disambig-names].  Without this the
        # emitter's half is worse than useless: nineteen AFP theories are
        # called `Examples`, and `beta/Examples` would fall to the stem
        # fallback and resolve to `alpha/Examples`, silently and confidently.
        # A label that looks paste-able and lands on a DIFFERENT theory is a
        # worse answer than a bare ambiguous name, which at least reads as
        # ambiguous.  Only a unique hit counts; anything else falls through.
        # Matched against the directory chain plus the declared theory NAME —
        # the exact tuple `render.theory_labels` builds the label out of, so
        # the two cannot drift.  (On disk the name is the stem, since Isabelle
        # requires it; a buffer-parsed section is where they part company.)
        want = tuple(Path(name).with_suffix("").parts)
        hits = [s for s in sections
                if (s.path.resolve().parent.parts
                    + (s.theory,))[-len(want):] == want]
        if len(hits) == 1:
            return hits[0]
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


def _resolve_binding(sections: list[TheorySection],
                     name: str) -> tuple[str, str] | None:
    """If `name` is an extra name bound by some declaration (see
    `Entry.bindings`), return `(parent name, phrasing)`; else None.  Lets
    callers/callees/show resolve such a name to the entry that binds it, and
    say *how* it is bound — an introduction rule and a `shows` conjunct
    resolve the same way but are not the same thing."""
    for sec in sections:
        for e in sec.entries:
            for n, kind in e.bindings:
                if n == name:
                    return e.name, _BINDING_KINDS[kind]
    return None


def cmd_theory(sections: list[TheorySection], name: str,
               flags: "CmdFlags") -> None:
    sec = _resolve_theory(sections, name)
    if sec is None:
        _fail_subject(f"no theory '{name}'.  Known theories:\n  "
                      + "\n  ".join(sorted(s.theory for s in sections)))
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


# `ISA_SYMBOL`, not `ISA_MARKUP`: this asks the LEXICAL question — is this an
# Isabelle symbol token? — and must answer yes for the structural symbols the
# name grammar refuses.  A user pasting `\<open>` into a pattern means the
# literal characters just as much as one pasting `\<^sub>`.
_PAT_MARKUP_RE = re.compile(ISA_SYMBOL)


def _user_pattern(pattern: str) -> str:
    r"""Make a user-typed search pattern mean what the user meant.

    Two rewrites, both for the same reason: a pattern that quietly matches
    nothing is worse than one that errors, because the user is told "no
    matches" and believes it.

    * Shell users reach for grep-style escaped alternation (``a\|b\|c``); in
      Python's ``re`` that is a literal ``|`` character.
    * An Isabelle name may contain markup — ``split\<^sub>i_tree`` — and query
      prints names that way, so it is what a user copies back in.  As a regex
      that is not merely imprecise, it is unmatchable: ``\<`` is a literal
      ``<`` and the ``^`` after it is a start-of-string ANCHOR sitting
      mid-pattern.  Over 120 AFP entries, 1,326 of the 1,691 markup-carrying
      names could not be found by their own printed spelling
      (`scripts/probe_symbol_names.py`).

    Only the ``\<...>`` spans are escaped, so the rest stays a regex and
    ``split\<^sub>i.*_smeq`` still means what it looks like.  This is also what
    makes the rewrite safe: ``\<`` has no other meaning in Python's ``re``
    (it is just ``<``), so no working pattern changes meaning.
    """
    pattern = pattern.replace(r"\|", "|")
    return _PAT_MARKUP_RE.sub(lambda m: re.escape(m.group(0)), pattern)


def _compile_user_pattern(pattern: str, flags: int = 0) -> "re.Pattern[str]":
    """`_user_pattern` + compile, reporting a bad regex instead of raising."""
    try:
        return re.compile(_user_pattern(pattern), flags)
    except re.error as exc:
        print(f"ERROR: invalid regex '{pattern}': {exc}", file=sys.stderr)
        sys.exit(2)


def _find_matches(sections: list[TheorySection], pat: "re.Pattern[str]",
                  statement: bool) -> list[Entry]:
    """Entries `pat` selects, in section order — one pattern's hit set.

    Factored out of :func:`cmd_find` so the conjunctive form can intersect
    several of these rather than reimplement what a match is.
    """
    matches: list[Entry] = []
    if statement:
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
                # A bound name counts: `rreqs` finds the record that declares
                # it, so the conjunction sees the same entry either way.
                if (pat.search(e.name)
                        or any(pat.search(c) for c in e.bound_names)):
                    matches.append(e)
    return matches


def cmd_find(sections: list[TheorySection], pattern: str,
             flags: "CmdFlags") -> None:
    pat = _compile_user_pattern(pattern, re.IGNORECASE)
    by_theory = _sections_by_theory(sections)
    matches = _find_matches(sections, pat, flags.statement)

    # `--statement` here selects the match locus, not the render: show the
    # matched entries the usual way (statement + proof preview).
    _emit_matches(by_theory, matches, pattern, flags)

    if flags.with_comments:
        # Additionally search inside preamble bodies and annotation
        # content, producing context windows.
        _emit_comment_matches(sections, [pat], pattern, flags)


def cmd_find_and(sections: list[TheorySection], patterns: list[str],
                 flags: "CmdFlags") -> None:
    r"""Conjunctive find: the entries matching **every** pattern, once
    [find-conjunction].

    The default for several patterns is a disjunction — run each search in
    turn, one report per pattern — which is the "batch of searches" idiom that
    replaces a shell loop.  The `find_theorems`-shaped question is the other
    one: *the* entry that mentions all of these.  Hunting a length lemma with
    `find --statement length encode_entry`, the first pattern alone returns
    every `length` in the corpus, so the answer arrives as
    `query find encode | grep length` — the pipe this tool exists to retire.

    Intersecting hit *sets* rather than and-ing the regexes is what makes it
    compose: the patterns may match different parts of the entry (one the
    name, one a bound name, one elsewhere in the statement) and in any order,
    which a single concatenated regex cannot express.
    """
    pats = [_compile_user_pattern(p, re.IGNORECASE) for p in patterns]
    by_theory = _sections_by_theory(sections)
    label = " AND ".join(patterns)

    matches = _find_matches(sections, pats[0], flags.statement)
    for pat in pats[1:]:
        keep = {id(e) for e in _find_matches(sections, pat, flags.statement)}
        matches = [e for e in matches if id(e) in keep]

    _emit_matches(by_theory, matches, label, flags)

    if flags.with_comments:
        # The conjunction carries over to prose, per line: a note is a hit only
        # if every pattern is on it.  Same rule as the entry side — one hit
        # satisfying all patterns — rather than a union that would quietly
        # reintroduce the OR the flag was asked to turn off.
        _emit_comment_matches(sections, pats, label, flags)


def _emit_comment_matches(sections: list[TheorySection],
                          pats: list["re.Pattern[str]"], label: str,
                          flags: "CmdFlags") -> None:
    hits = _find_in_comments(sections, pats[0], flags.context,
                             require=pats[1:])
    if hits:
        print()
        print(f"--- comment matches for '{label}' ({len(hits)} hit(s)) ---")
        for hit in hits:
            print(hit)


def _find_in_comments(sections: list[TheorySection], pat: re.Pattern,
                      context: int,
                      require: "list[re.Pattern[str]] | None" = None) -> list[str]:
    """Search inside text blocks and \\<comment> annotations across all
    theories.  Returns formatted hit strings: filename:line + context window.
    ``require`` (the conjunctive form) adds patterns that must ALSO match the
    same line or note, so one hit satisfies every pattern rather than the union
    satisfying them between them.
    """
    hits: list[str] = []
    extra = require or []

    def matched(text: str) -> bool:
        return bool(pat.search(text)) and all(r.search(text) for r in extra)

    for sec in sections:
        src = sec.source()
        # Text blocks (preambles + standalone)
        for tb_start, tb_end in sec.text_blocks:
            for ln in range(tb_start, tb_end + 1):
                if ln > len(src):
                    break
                line = src[ln - 1]
                if matched(line):
                    lo = max(tb_start, ln - context)
                    hi = min(tb_end, ln + context)
                    snippet = src[lo - 1:hi]
                    hits.append(f"\n{sec.theory}.thy:{ln} "
                                f"(in text block {tb_start}..{tb_end}):")
                    for j, snippet_line in enumerate(snippet, start=lo):
                        marker = ">" if j == ln else " "
                        hits.append(f"  {marker} {j}: {snippet_line}")
        # Inline \<comment> annotations: every note owned by an entry, not
        # just the proof-tagged ones.  A definition's notes are only reachable
        # this way — it has no proof, so it never had a roadmap to search.
        # The tag rides along in the locus so a hit says which part of the
        # entry the prose is about.
        for e in sec.entries:
            for ln, content, kind in e.annotations:
                if matched(content):
                    hits.append(f"\n{sec.theory}.thy:{ln} "
                                f"(\\<comment> in {e.name} {kind}): {content}")
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
        # Bound-name fallback (before substring): NAME may be an extra name
        # bound by a declaration — a `shows` conjunct, an introduction rule, a
        # mutually-declared constant; resolve to the entry that binds it.
        how = ""
        for s in sections:
            for e in s.entries:
                for n, kind in e.bindings:
                    if n == name:
                        matches.append(e)
                        how = _BINDING_KINDS[kind]
        if matches:
            parents = ", ".join(sorted({e.name for e in matches}))
            print(f"# '{name}' is {how} {parents}:")
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
        _fail_subject(f"no theory '{theory}'")
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
        _fail_subject(f"no theory '{theory}'")
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
        by_leaf = _leaf_index(by_theory)
        for s in sections:
            for imp in parse_thy_imports(s.path):
                resolved = _resolve_import(imp, by_theory, by_leaf)
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
        in_project = _import_depths(target.theory, by_theory, out_of_project)
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


def cmd_refs(sections: list[TheorySection], theory: str,
             flags: "CmdFlags") -> None:
    r"""What a theory **references**, rolled up from the citation graph.

    The complement of ``theory --names``, which lists what a theory *exports*.
    Every entry in the theory contributes its ``callees``, and the result is
    grouped by the theory that owns each cited name.

    This is finer-grained than ``deps`` / ``uses``, and the difference is the
    point.  Those work at the ``imports``-clause level — theory A declares that
    it imports theory B — which is a statement of intent.  This works at the
    citation level: which entries A's proofs actually invoke.  Comparing the
    two is what surfaces an import that is declared but never used, and the
    converse, a theory whose facts are cited without being imported directly
    (reached through the transitive closure, so it compiles, but the
    dependency is unstated).

    **Ownership is resolved through the importing theory's own closure**, not
    globally, because a name may be declared in several theories and the
    citing theory can only see some of them.  A declaration in the theory
    itself wins, then the nearest one by import depth, and only failing both
    does an arbitrary declaration get the credit.  Getting this wrong is not a
    cosmetic error: AODV declares each of its theories again under
    ``variants/``, so crediting the first in load order reported
    ``Aodv_Loop_Freedom`` as citing nothing from either of its two direct
    imports — the precise opposite of the truth, in the output whose whole
    purpose is that comparison.

    One approximation remains, inherited from the name-level graph: counts are
    **citing entries, not citation sites**.  ``callees`` is a set per entry, so
    "3" means three lemmas here need that name, not that it appears 3 times.
    """
    target = _resolve_theory(sections, theory)
    if target is None:
        _fail_subject(f"no theory '{theory}'")
        return

    graph_ = _build_call_graph(sections, flags.drop_names_upto,
                               reach=flags.reach)
    by_theory = _sections_by_theory(sections)
    own = target.theory
    closure = _import_depths(own, by_theory)

    # Every theory declaring each name, not just the first — the whole point
    # is to choose among them per citing theory.
    declared_in: dict[str, list[str]] = {}
    for sec in sections:
        for e in sec.entries:
            declared_in.setdefault(e.name, []).append(sec.theory)

    def owner_of(name: str) -> str:
        cands = declared_in.get(name)
        if not cands:
            return own
        if own in cands:            # a local declaration shadows an imported one
            return own
        visible = [(closure[c], c) for c in cands if c in closure]
        if visible:                 # nearest by import depth
            return min(visible)[1]
        return cands[0]

    tally: Counter[str] = Counter()
    for e in target.entries:
        for callee in graph_.callees.get(e.name, ()):
            tally[callee] += 1

    groups: dict[str, list[tuple[str, int]]] = {}
    for name, n in tally.items():
        owner = owner_of(name)
        if flags.external and owner == own:
            continue
        groups.setdefault(owner, []).append((name, n))
    for names in groups.values():
        names.sort(key=lambda kv: (-kv[1], kv[0]))

    total = sum(len(v) for v in groups.values())
    if flags.mode == "count":
        print(total)
        return
    if flags.mode == "names":
        # Bare names, one per line, so the output pipes straight back into
        # another query call.  Unique already: the tally is keyed by name.
        for name in sorted(n for v in groups.values() for n, _ in v):
            print(name)
        return

    if not total:
        scope = "cross-theory " if flags.external else ""
        print(f"{own} makes no {scope}references.")
        return

    # The import clause, for the declared-vs-used comparison.  Out-of-project
    # imports (`HOL-Library.*`) are not in the closure: their entries are not
    # indexed, so no citation of them could ever appear here and calling them
    # unreferenced would be an artefact of what query loads, not a fact about
    # the theory.
    declared = {t for t, d in closure.items() if d == 0}
    cited = set(groups) - {own}

    print(f"{own} references {total} name(s) "
          f"from {len(groups)} theory/theories:\n")
    order = sorted(groups, key=lambda t: (t == own, -len(groups[t]), t))
    width = max(len(t) for t in order)
    notes = {t: ("[self]" if t == own else
                 "[direct import]" if closure.get(t) == 0 else
                 f"[import depth {closure[t]}]" if t in closure else
                 "[not imported]")
             for t in order}
    note_w = max(len(n) for n in notes.values())
    for owner in order:
        print(f"  {owner:<{width}}  {notes[owner]:<{note_w}}  "
              f"{len(groups[owner])}")
        for name, n in groups[owner]:
            print(f"      {name}  ({n})")
        print()

    unused = sorted(declared - cited)
    if unused:
        print(f"  Direct imports no citation reaches ({len(unused)}): "
              f"{', '.join(unused)}")
    indirect = sorted(cited - declared)
    if indirect:
        print(f"  Cited but not directly imported ({len(indirect)}): "
              f"{', '.join(indirect)}")


def cmd_outline(sections: list[TheorySection], theory: str,
                flags: "CmdFlags") -> None:
    sec = _resolve_theory(sections, theory)
    if sec is None:
        _fail_subject(f"no theory '{theory}'")
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
                   external: bool = False, reach: str = "closure",
                   ) -> list[tuple[TheorySection, int, str]]:
    """Find proof-body usages of *name* across all .thy files.

    Returns a list of (section, line_no, line_text) triples.  The SECTION, not
    its theory name: the caller needs the hit's own source for the owner column
    and the `-U` context lines, and re-deriving it from the name through the
    last-wins `_sections_by_theory` index silently read both out of a DIFFERENT
    FILE whenever two theories share a name — 9,239 of `callers assms`' 161,426
    AFP rows print a line that does not occur in the section their owner column
    came from.  A wrong attribution, not an ambiguous label [disambig-loci].
    Filters out:
      - Whole theories that cannot SEE any declaration of *name* — it is
        declared elsewhere in the project and not in this theory's transitive
        in-project `imports` closure, so the token here means something else
        (`graph._Visibility`).  `reach="name"` restores name-only matching.
        A name the project declares nowhere is not filtered at all.
      - The definition site itself (same theory, within the entry's span).
      - Lines inside ``text \\<open>...\\<close>`` blocks (prose, not proof).
      - Antiquotation-only mentions: ``@{text name}``, ``@{thm name}``,
        ``@{term name}`` where the *only* occurrence of *name* on the line
        is inside an antiquotation.
      - When *name* is also a proof method or attribute (`simp`, `insert`,
        `mono`), lines that merely INVOKE it — `by simp`, `apply (auto simp:
        h)`, `[symmetric]`.  A method invocation is not a reference to the
        entry that happens to share its name, and reporting it as one made
        every such entry look heavily used.  The same positional rule the
        call graph applies (:func:`graph._shadowed_uses_on_line`), so
        `callers` and `unused` agree on what a use is.

    When ``external`` is true, additionally skip every line in the
    theory(ies) that define *name* — useful for "is anything outside
    Foo using Foo's primitives?" audits where intra-theory
    cross-references are noise.
    """
    word_re = re.compile(_isa_word_pattern(name))
    # Antiquotation pattern: @{text/thm/term/const "?name"?}
    antiq_re = re.compile(
        r'@\{(?:text|thm|term|const)\s+["\']?' + re.escape(name) + r'["\']?\}')

    # Shared infrastructure: per-section def-site ranges (for `name`) and
    # text-block ranges (prose to skip).  Both keyed by path, so `--external`
    # skips the FILES that declare `name` rather than every file that happens
    # to share their theory name [name-is-not-identity].
    all_def_sites = _build_def_sites(sections, {name})
    def_paths: set[Path] = {p for p, m in all_def_sites.items() if m}
    text_ranges = _noise_ranges(sections)
    # Read late: the namespace table is bound by the CLI after import.
    shadowed = name in _graph._NON_CITATION
    # A name an entry BINDS is a declaration of it here [bound-name-reach]:
    # `callers Bar` for a constructor is scoped to the theories that can see
    # the datatype, as it is for an entry.  The bulk graph does not do this
    # (it has no bound-name nodes), so `callers -r` / `callees` / `refs` /
    # `unused` totals are untouched.
    admits = _graph.site_filter(sections, name, reach)

    results: list[tuple[TheorySection, int, str]] = []
    for sec in sections:
        # External mode: skip every line in the defining theory(ies),
        # treating intra-theory cross-references as noise.
        if external and sec.path in def_paths:
            continue
        # Whole-theory visibility, tested once rather than per line: the
        # question is about the theory, not the site.
        if not admits(sec.theory):
            continue
        # Decide on the redacted view, report the raw one: a mention inside a
        # comment / `\<^cancel>` / inline ML body is not a use even when live
        # proof text shares its line, but the hit we print is the user's line.
        lines = sec.live_source()
        raw = sec.source()
        t_ranges = text_ranges.get(sec.path, [])
        d_ranges = all_def_sites.get(sec.path, {}).get(name, set())
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
            # A name shared with a proof method earns its mention positionally.
            if shadowed and not _shadowed_uses_on_line(line, {name}):
                continue
            results.append((sec, line_no, raw[line_no_0].rstrip()))
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

    The echoed locus is the theory's LABEL, not the token the user typed: a
    locus that came in as a path (`thys/Foo/Bar.thy:12`) goes back out in the
    house `theory:line` form, and one that came in bare goes back out
    qualified when the corpus holds two theories of that name.  Echoing the
    input verbatim would be the easy answer and the wrong one — the point of
    the echo is to say which theory the tool actually resolved to.
    """
    labels = locus_labels(sections)
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
        thy = labels.get(sec.path, sec.theory)
        loc = (f"{thy}:{lo}" if lo == hi
               else f"{thy}:{lo}..{hi_eff}")
        if lo > sec.thy_lines:
            print(f"{loc} → (past end of {thy} — "
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
            target = _format_target(entry)
            scope = f"{thy} ▸ {target}" if target else thy
            base = (f"{loc} → {entry.name} ({entry.tag}) — {scope} "
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
            target = _format_target(e)
            scope = f"{thy} ▸ {target}" if target else thy
            print(f"{loc} → {e.name} ({e.tag}) — {scope} "
                  f"{_format_extent(e)}")


@dataclass
class _SiteSubject:
    """A resolved `instances` / `codeqs` subject.

    ``how`` is non-empty when the name is one Isabelle MINTED rather than one
    the author wrote as a declaration name — a datatype constructor, a `shows`
    conjunct — resolved through the same bindings `_resolve_binding` reads.
    The SUBJECT stays the typed name: a code equation is about the
    constructor `Cons`, not about the `datatype list` that binds it.
    """
    name: str
    tag: str
    theory: str
    entry: Entry
    how: str = ""


def _resolve_site_subject(sections: list[TheorySection], name: str,
                          tags: frozenset[str], what: str
                          ) -> _SiteSubject | str:
    """The subject a site verb asks about, or the reason it cannot be asked.

    EVERY entry of that name is considered, not the first: a project
    routinely declares the same word twice (`rev` is a `primrec` in `List`
    and a locale-local LEMMA in `Groups_List`), and taking whichever came
    first turned a perfectly good subject into "is a LEMMA, not a constant".
    The right-kinded declaration wins; the wrong-kinded one is only what the
    diagnostic names.  Then a bound name whose BINDER is right-kinded (`Leaf`
    resolves because `datatype mytree` is a constant declaration); then the
    refusal.  No case folding and no substring fallback, unlike `show`.
    """
    found = [(sec.theory, e) for sec in sections for e in sec.entries
             if e.name == name]
    for theory, e in found:
        if e.tag in tags:
            return _SiteSubject(name, e.tag, theory, e)
    for sec in sections:
        for e in sec.entries:
            if e.tag not in tags:
                continue
            for n, kind in e.bindings:
                if n == name:
                    how = _BINDING_KINDS.get(kind, "bound by")
                    return _SiteSubject(name, e.tag, sec.theory, e,
                                        f"{how} {e.name}")
    if found:
        theory, e = found[0]
        return f"'{name}' is a {e.tag} in {theory}, not {what}"
    return f"'{name}' is not {what} declared in this project"


def _with_site_subject(sections: list[TheorySection], name: str,
                       tags: frozenset[str], what: str) -> _SiteSubject:
    """Resolve the subject or exit — the lookup family's contract one level
    in.  A subject the project does not declare is NOT an honest zero: the
    scan would find nothing for a typo and nothing for a locale declared in
    an imported session, and the caller could not tell either from a locale
    that genuinely has no instantiations.  A KNOWN subject with no sites
    keeps the honest zero, the same message shape and exit 0 `callers` gives
    an entry nothing calls.

    The `# 'X' is ...` note is printed here, ahead of the mode switch, so it
    appears in every mode — as `callers -r` already does for a bound name.
    """
    got = _resolve_site_subject(sections, name, tags, what)
    if isinstance(got, str):
        _fail_subject(got)
        raise SystemExit(EXIT_UNRESOLVED)  # unreachable; keeps the type honest
    if got.how:
        print(f"# '{name}' is {got.how}.")
    return got


def _emit_sites(sections: list[TheorySection],
                rows: list[tuple[_sites.Site, str]], name: str, noun: str,
                flags: 'CmdFlags', transitive: bool = False) -> None:
    """One renderer for both site verbs: LOCUS, NAME, KIND, [VIA,] source.

    The name sits exactly where `callers` and `methods` put their owning
    entry, and the locus stays FIRST, which is what keeps
    `instances L | awk '{print $1}' | xargs query enclosing` working and
    what `--names` prints on its own: for a SITE list the identity of a hit
    IS its locus, and `theory:line` is the tool's own span grammar.

    The locus is the qualified, suffix-free label (`render.theory_locus` of
    the site's own path) computed from one label map per run: a site is
    reported at a theory, the way a caller is, and on a corpus with two
    `Examples` the bare theory name was the one spelling `enclosing` could
    not resolve back to the row.

    The VIA column exists only under ``transitive``: without `-r` every row
    is a site of the subject, and a column repeating its name on every line
    would be noise — so the default listing is four columns, byte for byte.
    """
    sites = [s for s, _via in rows]
    if flags.mode == "count":
        print(len(sites))
        return
    labels = locus_labels(sections)
    loci = [f"{theory_locus(labels, s.path)}:{s.line}" for s in sites]
    if flags.mode == "names":
        for loc in loci:
            print(loc)
        return
    if not sites:
        print(f"No {noun}s found for '{name}'.")
        return
    names = [s.label(flags.sorts) for s in sites]
    vias = [via for _s, via in rows]
    loc_w = max(len(loc) for loc in loci)
    name_w = max(len(n) for n in names)
    kind_w = max(len(s.kind) for s in sites)
    via_w = max(len(v) for v in vias) if transitive else 0
    print(f"{len(sites)} {noun}(s) of {name}"
          f"{' (transitive)' if transitive else ''}:\n")
    for s, label, loc, via in zip(sites, names, loci, vias):
        via_cell = f"{via:<{via_w}}  " if transitive else ""
        print(f"  {loc:<{loc_w}}  {label:<{name_w}}  {s.kind:<{kind_w}}  "
              f"{via_cell}{s.text.strip()}")


def cmd_instances(sections: list[TheorySection], name: str,
                  flags: 'CmdFlags') -> None:
    """Where a locale or class is instantiated: the declared source sites."""
    _with_site_subject(sections, name, _sites.LOCALE_TAGS,
                       "a locale or class")
    # `-r` widens WHAT is asked about, not what counts as an answer: the
    # resolution and the exit contract are the same question either way, so
    # a subject with no transitive sites is the honest zero and an unknown
    # one is still a refusal.
    if flags.recursive:
        rows = _sites.find_instantiations_transitive(sections, name)
    else:
        rows = [(s, "") for s in _sites.find_instantiations(sections, name)]
    _emit_sites(sections, rows, name, "instantiation", flags,
                transitive=flags.recursive)


def cmd_callers(sections: list[TheorySection], name: str,
                flags: 'CmdFlags') -> None:
    """Print proof-body usages of a lemma/definition."""
    if flags.recursive:
        graph = _build_call_graph(sections, flags.drop_names_upto,
                                  reach=flags.reach)
        if name not in graph.all_names:
            bound = _resolve_binding(sections, name)
            if bound is not None:
                parent, how = bound
                print(f"# '{name}' is {how} {parent}; "
                      f"recursive caller closure operates at the {parent} "
                      f"(entry) level.")
                name = parent
            else:
                _fail_subject(f"'{name}' is not in the entry index")
                return
        reachable = _bfs_depths(lambda n: graph.callers.get(n, set()), {name})
        reachable.pop(name, None)
        _render_graph_results(sections, reachable, "caller", name, flags)
        return

    hits = _find_callers(sections, name, external=flags.external,
                         reach=flags.reach)
    if flags.mode == "count":
        print(len(hits))
        return
    if not hits:
        print(f"No callers found for '{name}'.")
        return
    n_after = max(0, flags.context)
    # Align the match loci into a column; each is a clean `theory:line` that
    # pastes into `enclosing` / `lines` / an editor (no trailing marker) — and
    # is qualified far enough to name one theory, so what pastes back is the
    # theory the row was found in [disambig-loci].
    labels = locus_labels(sections)
    loci = [f"{labels.get(s.path, s.theory)}:{ln}" for s, ln, _ in hits]
    loc_w = max((len(loc) for loc in loci), default=0)
    print(f"{len(hits)} caller(s) of {name}:\n")
    for (sec, line_no, text), loc in zip(hits, loci):
        encl = _enclosing_entry(sec, line_no)
        print(f"  {loc:<{loc_w}}  {_owner_field(encl)}  {text.strip()}")
        if n_after > 0:
            src = sec.source()
            # 1-indexed line_no → 0-indexed slice start at line_no
            # (i.e., the line *after* the match).  Context keeps ripgrep's
            # `-` marker — it flags the line as context, not a match, and
            # `_parse_locus` strips it so the locus still round-trips.
            label = loc.rsplit(":", 1)[0]
            for off, ctx in enumerate(src[line_no:line_no + n_after], start=1):
                ctx_no = line_no + off
                print(f"  {label}:{ctx_no}-  {ctx.rstrip()}")


def cmd_callees(sections: list[TheorySection], name: str,
                flags: 'CmdFlags') -> None:
    """Entry-level forward edge: the entries this entry references in
    its proof body (its callees).  Pairs with `cmd_callers` (reverse).
    Not to be confused with the theory-level `deps` / `uses` pair."""
    graph = _build_call_graph(sections, flags.drop_names_upto,
                              reach=flags.reach)
    if name not in graph.all_names:
        bound = _resolve_binding(sections, name)
        if bound is not None:
            parent, how = bound
            print(f"# '{name}' is {how} {parent}; "
                  f"reporting {parent}'s callees (shared proof body).")
            name = parent
        else:
            _fail_subject(f"'{name}' is not in the entry index")
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
    #
    # Two authorities, and both are needed.  `counts` says the project uses NAME
    # in introducer position, which since [introducer-no-table] includes tactics
    # the table cannot carry — an entry's own Eisbach/ML method (`auto2`,
    # `regexp`).  Gating on the table alone refused to locate exactly the methods
    # the tally had just reported, so the two verbs contradicted each other.
    # The table is still consulted, for the opposite case: a genuine method that
    # this project happens not to use should answer "no uses", not "not a
    # method".  Failing both is the only real error — and it must stay an error,
    # because a mistyped name would otherwise get "No uses found", an empty
    # success for a question that was never asked.
    if name not in counts and name not in graph._PROOF_METHODS:
        _fail_subject(f"'{name}' is not used as a proof method here, and is "
                      f"not in the resolved proof-method namespace.  Try "
                      f"`methods` for the list of methods actually used.")
    if flags.mode == "count":
        print(len(located))
        return
    if not located:
        print(f"No uses of method '{name}' found.")
        return
    labels = locus_labels(sections)
    loci = [f"{labels.get(p, p.stem)}:{ln}" for p, ln, *_ in located]
    loc_w = max((len(loc) for loc in loci), default=0)
    if flags.mode == "names":
        for (_p, _ln, owner, _text), loc in zip(located, loci):
            print(f"  {loc:<{loc_w}}  {_owner_field(owner)}")
        return
    print(f"{len(located)} use(s) of method '{name}':\n")
    for (_p, _ln, owner, text), loc in zip(located, loci):
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
    depth = 1
    while True:
        # LEVEL-SYNCHRONISED: every test in this pass is against the frontier
        # as it stood BEFORE the pass.  Re-reading a set the loop body is
        # growing gave a name whose only caller was marked earlier in the same
        # pass its caller's depth instead of one more — so how far a chain
        # collapsed depended on the order names came out of `all_names`, i.e.
        # on the process's string hash seed.  Snapshotting also makes the
        # result independent of visit order, which is what lets two runs of a
        # build-hygiene check be diffed at all.
        frontier = set(unused)
        newly = [name for name in graph.all_names - frontier - keep
                 if (callers := graph.callers.get(name, set()))
                 and callers <= frontier]
        if not newly:
            return unused
        for name in newly:
            unused[name] = depth
        depth += 1


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
    label = "transitively unused" if recursive else "unused"
    total = len(entries)

    # Before the empty guard [count-mode-zero]: a project with nothing unused
    # has ZERO unused entries, and that is the answer a script wants — the one
    # case it most wants to branch on, and the one that used to be a sentence.
    if flags.mode == "count":
        print(total)
        return

    if not entries:
        print("No unused entries found.")
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
    # pins exactly that, and `callers foo` keeps meaning `foo`.  Deadness, though,
    # is a question about the DECLARATION: deleting `definition foo` breaks every
    # proof citing `foo_def`, so such a proof keeps `foo` alive.  Asking the
    # fact-level question here would report live definitions as dead.
    graph = _build_call_graph(sections, flags.drop_names_upto, derived=True,
                              reach=flags.reach)

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
                   ) -> list[tuple[Path, int, str, "Entry | None", bool, bool]]:
    """Walk every section's source and return one tuple per line that
    matches `pat`.  Each tuple is (path, line_no, line_text,
    owning_entry, is_live, is_thy).

    The section's PATH, not a display name: these two verbs report a FILE, and
    a bare file name is ambiguous over a corpus in exactly the way a bare
    theory name is (nineteen AFP files are called `Examples.thy`).
    `render.file_locus` turns the path into the printed locus — the label with
    its suffix restored, so a non-`.thy` positional still reports its actual
    filename rather than `<stem>.thy` [disambig-loci].

    `is_thy` is False for non-`.thy` positionals (Markdown / prose),
    which have no Isabelle entries and hence no owning-entry column —
    `cmd_grep` shows the matched line text directly for those.

    is_live = True iff the line is genuine proof / declaration source —
    not inside a top-level `text \\<open>...\\<close>` block, not inside
    a per-entry preamble (a small text block attached to a following
    declaration), not inside a multi-line `\\<comment>
    \\<open>...\\<close>` annotation, and not inside one of the lexical
    non-Isar regions (`(* ... *)`, `\\<^cancel>`, legacy `{* ... *}`
    verbatim, an ML body — `parsing.extract_nonisar_ranges`).

    owning_entry is the lemma/theorem/definition whose span contains the
    matching line, via binary-search lookup (None if the line is outside
    any indexed entry — e.g. between top-level declarations).
    """
    line_index = _build_line_index(sections)
    out: list[tuple[str, int, str, Entry | None, bool, bool]] = []
    for sec in sections:
        lines = sec.source()
        live_lines = sec.live_source()
        noise = [range(lo, hi + 1) for lo, hi in _noise_spans(sec)]
        idx = line_index.get(sec.path, [])
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
            # Live iff the match survives redaction, not merely iff the LINE
            # does.  `by simp \<comment> \<open>see foo\<close>` is a live line
            # holding a prose-only match, and a line-granular test would report
            # that `foo` as source.  Searching the redacted copy asks the
            # question at the right granularity — the raw line is still what
            # gets matched first, so `--with-comments` still finds prose.
            is_live = (not any(line_no in r for r in noise)
                       and bool(pat.search(live_lines[line_no_0])))
            owner = _entry_at_line(idx, line_no)
            out.append((sec.path, line_no, line.rstrip(), owner,
                        is_live, sec.is_thy))
    return out


def cmd_grep(sections: list[TheorySection], pattern: str,
             flags: 'CmdFlags') -> None:
    """Regex-search live source across all theories.

    Default: only matches in live source (declarations + proof bodies),
    skipping `text \\<open>...\\<close>` blocks, per-entry preambles, and every
    lexical non-Isar region — `(* ... *)`, `\\<comment>` notes, `\\<^cancel>`,
    legacy verbatim, ML bodies.  The test is per MATCH, not per line, so a hit
    that sits only inside a note trailing live proof text is prose.  Use
    `--with-comments` to also include prose matches; each non-live hit is
    tagged.

    The pattern is read by `_user_pattern`, exactly as `cmd_find` reads its
    own: shell-grep alternation (`a\\|b\\|c`) and Isabelle markup
    (`\\<^sub>`) both mean here what they look like.
    """
    pat = _compile_user_pattern(pattern)

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

    labels = locus_labels(sections)
    loci = [f"{file_locus(labels, p)}:{ln}" for p, ln, *_ in hits]
    loc_w = max((len(loc) for loc in loci), default=0)

    if flags.mode == "names":
        # Compact: location + owning entry, no source line.  For a
        # non-`.thy` positional there is no owning entry, so names mode
        # would be content-free — fall back to the matched line text.
        for (_p, _ln, text, owner, is_live, is_thy), loc in zip(hits, loci):
            marker = "" if is_live else "  [in comment/text]"
            if not is_thy:
                print(f"  {loc:<{loc_w}}  {text.strip()}{marker}")
                continue
            print(f"  {loc:<{loc_w}}  {_owner_field(owner, span=False)}{marker}")
        return

    # Default: location + owning entry + matched line text.  Non-`.thy`
    # positionals have no entry column — show the line inline on one row.
    for (_p, _ln, text, owner, is_live, is_thy), loc in zip(hits, loci):
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
    labels = locus_labels(sections)
    loci = [f"{file_locus(labels, p)}:{ln}" for p, ln, *_ in hits]
    loc_w = max(len(loc) for loc in loci)
    for (_p, _ln, _text, owner, _live, _is_thy), loc in zip(hits, loci):
        print(f"  {loc:<{loc_w}}  {_owner_field(owner, span=False)}")
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

    # Qualified against the LOADED CORPUS, not against the rows on screen
    # [disambig-names].  Scoping to the shown rows is the tempting reading and
    # it breaks the round-trip: whether `Examples:11` names one theory is a
    # fact about the corpus — nineteen AFP theories are called `Examples` — not
    # about which of them a `-N 8` happened to print.  A label that is unique
    # on screen and ambiguous on paste is worse than no label.
    #
    # A single-session run still shows bare `Bla`, because the qualification is
    # driven by actual collisions and a session has none.
    shown = rows[:top]
    labels = locus_labels(sections)
    print(f"Top {len(shown)} largest entries:\n")
    print(f"{'Lines':>6}  {'Tag':<8}  {'Name':<42}  Theory  (span)")
    print(f"{'-' * 6:>6}  {'-' * 8:<8}  {'-' * 42:<42}  ------")
    for size, e, s in shown:
        theory = labels.get(s.path, s.theory)
        print(f"{size:>6}  {e.tag:<8}  {e.name:<42}  {theory}  ({e.src_start}..{e.thy_end})")


# --- machine-readable graph export [graph-export] --------------------------
#
# One whole-graph verb rather than a `--json` flag on each of
# `callers`/`callees`/`deps`/`uses`.  The consumers named for this — `jq`,
# Graphviz, external analysis — want the adjacency in full, which those verbs
# cannot give: each answers about ONE subject, so reconstructing the graph from
# them means N invocations and a merge.  The flag route also multiplies the
# output contract by six, across renderers that already differ; scripted
# single-subject answers are what `--names` / `-c` are for.

def _dot_quote(s: str) -> str:
    r"""A DOT-safe double-quoted ID.

    Isabelle names routinely carry backslashes (`split\<^sub>i_tree`), and DOT
    reads `\` as an escape introducer inside a quoted ID, so an unescaped name
    is not merely ugly — `\<` would be consumed and the graph would carry a
    different name than the corpus does.
    """
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _citation_graph_data(sections: list[TheorySection],
                         flags: "CmdFlags") -> dict:
    """Nodes = indexed entries; edges = caller -> callee."""
    g = _build_call_graph(sections, flags.drop_names_upto, reach=flags.reach)
    by_name = _entry_by_name(sections)
    nodes = [{"name": n, "theory": by_name[n][0], "tag": by_name[n][1].tag,
              "line": by_name[n][1].thy_line}
             for n in sorted(g.all_names) if n in by_name]
    known = {n["name"] for n in nodes}
    edges = sorted((caller, callee)
                   for caller, callees in g.callees.items()
                   if caller in known
                   for callee in callees if callee in known)
    return {"kind": "citation", "nodes": nodes,
            "edges": [list(e) for e in edges]}


def _import_graph_data(sections: list[TheorySection]) -> dict:
    """Nodes = theories; edges = importer -> imported.

    Out-of-project imports (`HOL-Library.*`, another entry) are kept as nodes
    flagged ``external``, not dropped.  They are a real part of the picture a
    dependency diagram is for, and query knows their raw token even though it
    does not load their sources.
    """
    by_theory = _sections_by_theory(sections)
    nodes = [{"name": s.theory, "external": False,
              "lines": s.thy_lines, "entries": len(s.entries)}
             for s in sorted(sections, key=lambda s: s.theory)]
    edges: list[tuple[str, str]] = []
    external: set[str] = set()
    by_leaf = _leaf_index(by_theory)
    for sec in sections:
        for imp in parse_thy_imports(sec.path):
            resolved = _resolve_import(imp, by_theory, by_leaf)
            if resolved is None:
                external.add(imp)
                edges.append((sec.theory, imp))
            else:
                edges.append((sec.theory, resolved))
    nodes += [{"name": n, "external": True} for n in sorted(external)]
    return {"kind": "imports", "nodes": nodes,
            "edges": [list(e) for e in sorted(set(edges))]}


def cmd_graph(sections: list[TheorySection], kind: str, fmt: str,
              flags: "CmdFlags") -> None:
    """Emit the whole citation or import graph as JSON or DOT.

    ``kind`` is ``citation`` (entry names, from the call graph) or ``imports``
    (theories, from the `imports` clauses) — the two graphs the tool already
    builds, which `callers`/`callees` and `deps`/`uses` respectively read one
    node at a time.
    """
    data = (_citation_graph_data(sections, flags) if kind == "citation"
            else _import_graph_data(sections))

    if fmt == "json":
        # Sorted and indented: the output of two runs over the same tree must
        # diff cleanly, which is most of what makes an export worth having.
        print(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False))
        return

    ext = {n["name"] for n in data["nodes"] if n.get("external")}
    print(f"digraph {data['kind']} {{")
    print("  rankdir=LR;")
    for n in data["nodes"]:
        attrs = ' [style=dashed]' if n["name"] in ext else ''
        print(f"  {_dot_quote(n['name'])}{attrs};")
    for src, dst in data["edges"]:
        print(f"  {_dot_quote(src)} -> {_dot_quote(dst)};")
    print("}")
