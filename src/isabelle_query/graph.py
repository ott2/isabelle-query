"""Call graph, usage analysis, and the shared line-level lookups.

The third layer of the module DAG (above ``parsing``, below ``render`` /
``commands``).  Everything here answers a *usage* question over the parsed
index rather than a text question over source:

* line→entry attribution (``_build_line_index`` / ``_entry_at_line``) and the
  name indices (``_sections_by_theory`` / ``_entry_by_name``);
* the prose/def-site exclusion masks shared by single-name search and bulk
  graph construction (``_noise_spans`` / ``_noise_ranges`` / ``_build_def_sites``);
* the citation router (``_is_citation_name`` / ``_NON_CITATION``) and the
  single-pass name-level call graph (``_build_call_graph``);
* the proof-method census (``_scan_methods``), the router's complement — the
  tokens ``_is_citation_name`` rejects as fact edges are the method uses it
  tallies;
* the in-project ``imports`` closure (``_resolve_import`` /
  ``_import_depths``), which is what "can this theory SEE that declaration"
  is asked of;
* the one breadth-first walk behind every ``-r`` form (``_bfs_depths``).

Depends on ``model``, ``parsing`` (for the ``_line_mask`` primitive), the
Isabelle namespace tables, and ``isabelle_layout``'s ``parse_thy_imports`` —
never on rendering or the CLI.
"""

from __future__ import annotations

import re
from bisect import bisect_right
from collections import Counter
from collections.abc import Callable, Iterable
from operator import itemgetter
from pathlib import Path

from isabelle_query import _census_namespace as _census_ns
from isabelle_query import _isabelle_namespace as _isa_ns
from isabelle_query.model import (
    CallGraph,
    Entry,
    TheorySection,
    _CITABLE_TAGS,
    _DROP_NAMES_UPTO,
)
from isabelle_layout import parse_thy_imports
from isabelle_query.parsing import ISA_SYMBOL, ISA_WORD_CHAR, _line_mask


def _build_line_index(sections: list[TheorySection]
                      ) -> dict[Path, list[tuple[int, int, Entry]]]:
    """For each theory, build a sorted list of (src_start, thy_end, Entry)
    for binary-search lookup of which entry owns a given line.  The span
    starts at ``src_start`` (the leading preamble, if any) so a doc line
    resolves to the entry it documents, not the preceding one.

    Keyed by the section's PATH [name-is-not-identity].  A theory name is not
    an identity over a corpus — 461 AFP names are shared — and this map is
    written by one loop over the sections and read back by another, so a
    name key silently handed 758 sections another file's spans.  381,710 of
    the 449,860 lines in those sections got a different owner that way.
    """
    index: dict[Path, list[tuple[int, int, Entry]]] = {}
    for sec in sections:
        spans = [(e.src_start, e.thy_end, e) for e in sec.entries
                 if e.thy_line > 0]
        # Sort on the two integers ONLY.  A bare `spans.sort()` compares the
        # third component whenever the first two are equal, and `Entry` has no
        # ordering — so one `axiomatization` declaring several names on a line
        # (four such pairs in FOL/ex/Locale_Test/Locale_Test1) raised
        # `TypeError` and killed every verb that builds this index.  The sort
        # is stable, so equal spans keep source order.
        spans.sort(key=lambda s: (s[0], s[1]))
        index[sec.path] = spans
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
    the document blocks (``text``/``text_raw``/``txt``), section **headings**,
    per-entry preambles, and the lexical non-Isar regions (``(* ... *)``
    comments, ``\<^cancel>``, ``\<comment>`` marginal notes, legacy
    ``{* ... *}`` verbatim and ML bodies — `parsing.extract_nonisar_ranges`).
    The single definition of "prose, not proof" — `grep`, `methods`, the call
    graph (via `_noise_ranges`), and the proof-block drill-down all skip exactly
    these lines, so the notion can no longer drift between them.

    ``sec.heading_spans`` is a separate field from ``text_blocks`` and unioned
    only here: both are prose to a *scanner*, but only the latter can be a
    declaration's docstring.  Headings were in neither list, which made
    ``section \<open>Consequences proved using helper\<close>`` an edge to
    `helper` — 36,342 heading lines corpus-wide were being read as Isar.

    ``sec.comment_ranges`` is deliberately NOT unioned in, though it names the
    same ``\<comment>`` annotations: it is line-granular, and a marginal note
    normally TRAILS live proof text (``by simp \<comment> \<open>why\<close>``).
    Including it dropped the `by simp` with the note — a true citation lost,
    the direction this project treats as the worse one.  The tokenizer reports
    the same regions by column, so `nonisar_ranges` covers the lines that are
    wholly a note and `live_source` blanks the rest in place.
    """
    return (list(sec.text_blocks) + list(sec.heading_spans)
            + list(sec.nonisar_ranges)
            + [e.preamble for e in sec.entries if e.preamble])


def _noise_ranges(sections: list[TheorySection]) -> dict[Path, list[range]]:
    r"""Per-section ``range`` objects for the non-live (prose) line spans —
    each section's :func:`_noise_spans` as ``range``s for membership tests.
    Used by single-name search (`_find_callers`) and bulk graph construction
    (`_build_call_graph`) — the oracle shares it — so both treat
    ``text``/``\<comment>``/preamble mentions as documentation, not calls.

    Keyed by PATH, like the other two per-section indexes: this one decides
    prose-vs-live, so a collapsed key does not merely misattribute a hit but
    SUPPRESSES a real one and admits a fake one.  38,068 lines of the AFP were
    classified the wrong way round [name-is-not-identity].
    """
    return {sec.path: [range(lo, hi + 1) for lo, hi in _noise_spans(sec)]
            for sec in sections}


def _build_def_sites(sections: list[TheorySection],
                     names: set[str] | None = None,
                     ) -> dict[Path, dict[str, set[range]]]:
    """Per-section map of definition-site line ranges, keyed by entry name.

    Used to exclude the definition itself from a search for references
    to that name.  When ``names`` is given, only those names are tracked;
    otherwise every entry with a source location is included.

    Result shape: ``def_sites[path][name] = {range(thy_line, thy_end+1), ...}``
    — by PATH, for the reason in :func:`_build_line_index`, and with the same
    suppressing effect as :func:`_noise_ranges`: another file's def sites
    exclude lines that are genuine citations here [name-is-not-identity].
    """
    def_sites: dict[Path, dict[str, set[range]]] = {}
    for sec in sections:
        site_map: dict[str, set[range]] = {}
        for e in sec.entries:
            if e.thy_line <= 0:
                continue
            if names is None or e.name in names:
                site_map.setdefault(e.name, set()).add(
                    range(e.thy_line, e.thy_end + 1))
            # An extra bound name's declaration site is its parent's span, so
            # `callers NAME` excludes the `shows ... and C:` / `| r1: "..."` /
            # `and g ::` line that declares it.  Without this the declaration
            # reads as a citation of itself.  Restricted to explicitly-queried
            # names (never the names=None broad pass) so these don't leak into
            # the call-graph universe.
            if names is not None:
                for c in e.bound_names:
                    if c in names:
                        site_map.setdefault(c, set()).add(
                            range(e.thy_line, e.thy_end + 1))
        def_sites[sec.path] = site_map
    return def_sites


# Method-argument modifiers parsed inline by individual methods, so they have
# no declaration site of their own (and are absent from _isabelle_namespace);
# a short, auditable tier-2 list to go with the source-derived namespaces.
_ARG_MODIFIERS = frozenset({"add", "del", "only", "OF", "THEN"})

# The router's namespace tables — the single reconfigurable source of truth for
# every consumer (this module, `commands`' method verb, `shape`'s identifier
# classifier).  They start bound to a *committed* table so **import stays pure**:
# importing the package spawns no Isabelle and stats no heap, which is what keeps
# `query` startup sub-100ms and — crucially — keeps every direct-call test
# deterministic regardless of whether Isabelle is installed on the machine
# running the suite.  `configure_namespace()` rebinds them once, at CLI dispatch,
# after a caller has resolved a runtime-dumped table; nothing rebinds them at
# import time.
#
# WHICH committed table is a separate question from committed-vs-dumped, and the
# answer is the **broad HOL-family union** (`_census_namespace`), not the minimal
# Pure floor: the default a *library* caller gets must be the one the CLI gets.
# `cli._configure_namespace` binds the union unconditionally for `shape census`
# and — via `_bind_committed_fallback` — for any HOL-base project with no built
# heap, which is the common case.  So the Pure floor was a table almost no CLI run
# ever saw, yet it was what `import isabelle_query` handed every direct caller,
# and the gap was silent, large and one-directional: over 40 AFP entries /
# 102,927 steps the floor extracted a `Step.method` on 23.1% of steps against the
# union's 53.5%, dropping `auto`/`blast`/`metis`/`induct` and with them the
# `trivial_frac` of 62.3% of proofs — always toward "discharges nothing"
# (`scripts/probe_library_namespace.py`).  A broader table is safe here because
# `_leading_method`/`_scan_methods` read it in *introducer* position only, where a
# match is a real method by construction; the one position-blind consumer
# (`shape.classify_identifier`) measured Δ=0 against per-entry-exact tables.
# `use_pure_namespace()` restores the floor, which only a positively non-HOL
# project wants.
_PROOF_METHODS = _census_ns.PROOF_METHODS
_ATTRIBUTES = _census_ns.ATTRIBUTES
# Keywords are logic-invariant (Pure outer syntax), so there is only ever one
# table for them and `_census_namespace` deliberately carries none.
_KEYWORDS = _isa_ns.KEYWORDS
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
_NON_CITATION = (_PROOF_METHODS | _ATTRIBUTES | _KEYWORDS | _ARG_MODIFIERS)


def configure_namespace(methods, attributes, keywords) -> None:
    """Rebind the router's namespace tables and rebuild the derived reject-set.

    The one seam through which a resolved (e.g. runtime-dumped) Isabelle
    namespace reaches the router.  **The package never calls it at import** — the
    module-level bindings default to the committed broad union, so importing
    spawns nothing and every direct-call test sees a fixed table; the CLI binds
    at dispatch, and a library caller may bind whenever it likes (see
    :func:`use_census_namespace` / :func:`use_pure_namespace` for the two
    committed tables).  `commands` (the `methods` verb) and `shape` (its
    identifier classifier) read these same globals late-bound, so one call
    reconfigures all three consumers coherently.  `keywords` is passed through
    unchanged — the dump supplies only methods/attributes; keywords stay the
    declarative Pure.thy table, which there is no reason to reinvent.
    """
    global _PROOF_METHODS, _ATTRIBUTES, _KEYWORDS, _NON_CITATION
    _PROOF_METHODS = frozenset(methods)
    _ATTRIBUTES = frozenset(attributes)
    _KEYWORDS = frozenset(keywords)
    _NON_CITATION = _PROOF_METHODS | _ATTRIBUTES | _KEYWORDS | _ARG_MODIFIERS


def use_census_namespace() -> None:
    """Bind the broad committed HOL-family union — **the import-time default**.

    The supported way back to the default after a caller has bound something
    else, and the table ``shape census`` binds unconditionally so its output
    regenerates identically anywhere.  A library caller measuring a HOL project
    needs no call at all; this exists so that "put it back" is a supported
    operation rather than reaching into ``_census_namespace``.
    """
    configure_namespace(_census_ns.PROOF_METHODS, _census_ns.ATTRIBUTES,
                        _isa_ns.KEYWORDS)


def use_pure_namespace() -> None:
    """Bind the minimal committed Pure floor (37 methods: ``simp``, ``rule``,
    ``unfold``, …; **no** ``auto``/``blast``/``induct``, which are HOL's).

    For a positively non-HOL project — ``ZF``, ``FOL``, ``Pure`` — where the HOL
    union would assert methods this logic does not have.  ``cli._bind_committed_
    fallback`` calls it for exactly that case.  On a HOL project this floor
    *silently* under-extracts ``Step.method``, so prefer a session-exact table
    (:func:`configure_namespace`) or the default union.
    """
    configure_namespace(_isa_ns.PROOF_METHODS, _isa_ns.ATTRIBUTES,
                        _isa_ns.KEYWORDS)


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


_WORD_RE = re.compile(r"[\w']+")


def _shadowed_uses_on_line(line: str, names: set[str],
                           derived: bool = False) -> set[str]:
    """Which of `names` this line genuinely USES.

    `names` are declared entries whose spelling is also a proof method or
    attribute (`lemma foo` where `foo` is an Eisbach method; `definition simp`).
    The position-blind scan cannot tell `by simp` from a use of such an entry,
    which is why these names were once dropped from the graph altogether — at
    the cost of every real citation of them.  Position settles it, and only for
    this rare subset, so the line is re-read only when one is present.

    A mention counts as a use when it is either

    * an explicit fact citation — `using foo`, `by (rule foo)`, `simp add: foo`
      (:func:`_cited_facts_on_line`, which reads fact-argument positions only), or
    * inside a quoted proposition or cartouche — `lemma "simp x = y"` — where
      the token is a constant or statement text, never a method invocation.

    Everything else — `by simp`, `apply (auto simp: h)`, `[symmetric]` — is the
    method or attribute of that name doing its job, and mints no edge.
    """
    cited, _ = _cited_facts_on_line(line)
    if derived:
        cited = cited | {n for n in names
                         if n + "_def" in cited or n + "_defs" in cited}
    used = names & cited
    rest = names - used
    if rest and ('"' in line or "\\<open>" in line):
        terms = " ".join(a or b for a, b in _PROP_TEXT_RE.findall(line))
        if terms:
            used = used | (rest & set(_WORD_RE.findall(terms)))
    return used


def _theory_leaf(name: str) -> str:
    """The last path segment of a theory name or ``imports`` token — what
    ``Thy_Header.import_name`` keeps.  ``"../BV/Altern"`` and ``"Altern"``
    denote the same theory to Isabelle, and so must here [import-leaf]."""
    return name.replace("\\", "/").rsplit("/", 1)[-1]


def _leaf_index(sec_by_name: dict[str, TheorySection]) -> dict[str, list[str]]:
    """``{leaf: [theory names carrying a path]}``, for resolving an import
    written bare against a theory a ROOT spelled with a directory.

    Only names that are *not* already their own leaf go in, so this can never
    shadow a plain name — an exact match is tried first and always wins.  It
    stays small for that reason: 56 of `src/HOL`'s 1,451 theories.
    """
    idx: dict[str, list[str]] = {}
    for name in sec_by_name:
        leaf = _theory_leaf(name)
        if leaf != name:
            idx.setdefault(leaf, []).append(name)
    return idx


def _import_candidates(imp: str, sec_by_name: dict[str, TheorySection],
                       by_leaf: dict[str, list[str]] | None = None
                       ) -> list[str]:
    """Every in-project theory an ``imports`` token could denote, most
    specific spelling first; empty when the token is external.

    `parse_thy_imports` returns tokens verbatim, but the section index
    (`sec_by_name`) is keyed by theory name.  Four spellings reach a loaded
    theory, tried in order:

    * bare, matching directly (``Substrate``);
    * session-qualified, by the tail after the last ``.``
      (``Proj_Base.Substrate``);
    * **path-spelled, by its leaf** — ``imports "../WFair"``
      (HOL/UNITY/Simple/Token.thy:10), ``imports
      "variants/a_norreqid/A_Aodv_Loop_Freedom"`` (AFP/AODV/All.thy);
    * **bare against a path-spelled THEORY** — a ROOT that says
      ``theories "Simple/Reach"`` gives the section that name, so a sibling's
      ``imports Reach`` matches nothing without `by_leaf`.

    The last two are the same rule seen from either end, and it is Isabelle's
    (`Thy_Header.import_name` takes the last segment).  Without them the token
    is classified external — cosmetic for ``deps``, but a HOLE in the
    visibility closure, which may only DROP and so deletes every citation
    across the edge in silence: 2,803 over `src/HOL` and 65,745 over the AFP
    [import-leaf].

    A genuinely external import (``HOL-Library.FuncSet``) names no in-project
    theory by any of the four, so the list is empty and the caller keeps the
    *raw* token for the ``[out-of-project]`` line.  The leaf rules add no new
    way to mistake one for a local theory: they fire only when the token or a
    loaded name contains ``/``, which an external session-qualified import
    never does.

    Several candidates are returned only for the last rule, where two ROOTs
    spelled distinct theories with the same leaf.  Callers that must print one
    dependency take :func:`_resolve_import`; the visibility closure takes them
    all, because it may only drop and a union is the safe side.

    `by_leaf` is :func:`_leaf_index` of the same map.  Pass it when resolving
    in a loop — deriving it per call is a pass over every theory name.
    """
    if imp in sec_by_name:
        return [imp]
    if "." in imp:
        tail = imp.rsplit(".", 1)[1]
        if tail in sec_by_name:
            return [tail]
    leaf = _theory_leaf(imp)
    if "." in leaf:
        leaf = leaf.rsplit(".", 1)[1]
    if leaf != imp and leaf in sec_by_name:
        return [leaf]
    if by_leaf is None:
        by_leaf = _leaf_index(sec_by_name)
    return sorted(by_leaf.get(leaf, ()))


def _resolve_import(imp: str, sec_by_name: dict[str, TheorySection],
                    by_leaf: dict[str, list[str]] | None = None) -> str | None:
    """The one in-project theory an ``imports`` token denotes, or ``None``.

    :func:`_import_candidates` narrowed to a single answer for the verbs that
    print a dependency (``deps``, ``uses``, ``graph imports``), which need one
    edge per import clause rather than a set.  Where the token is genuinely
    ambiguous the first candidate in name order is taken, deterministically.
    """
    got = _import_candidates(imp, sec_by_name, by_leaf)
    return got[0] if got else None


def _import_depths(start: str, by_theory: dict[str, TheorySection],
                   out_of_project: set[str] | None = None) -> dict[str, int]:
    """``{theory: depth}`` over the in-project imports graph from `start`.

    Depth 0 is a *direct* import, 1 an import of an import, and so on; `start`
    itself is excluded.  When `out_of_project` is given, every import that does
    not resolve to a loaded theory (``HOL-Library.*``, another entry) is
    collected into it rather than walked.

    Shared by ``deps -r``, which reports the closure, and ``refs``, which uses
    it to decide which of several declarations of a name the citing theory can
    actually see.  It lives here rather than in ``commands`` because that
    second question is not a rendering concern: it is what the citation
    attribution below has to ask, and a helper one layer up could not be asked
    it [citation-reach].

    Single-valued, like the ``deps`` output it feeds: where a name is declared
    twice this walks the last-wins section, and where a leaf is ambiguous it
    takes one candidate.  The *filter* cannot afford either narrowing and does
    not make them — see :class:`_Visibility`.
    """
    by_leaf = _leaf_index(by_theory)

    def imports_of(name: str) -> list[str]:
        sec = by_theory.get(name)
        if sec is None:
            return []
        children: list[str] = []
        for imp in parse_thy_imports(sec.path):
            child = _resolve_import(imp, by_theory, by_leaf)
            if child is None:
                if out_of_project is not None:
                    out_of_project.add(imp)
            else:
                children.append(child)
        return children

    depths = _bfs_depths(imports_of, [start], seed_depth=-1)
    depths.pop(start, None)
    return depths


# --- Visibility: can a site in theory T name a declaration in theory D? ----
#
# A NECESSARY condition, not a sufficient one, so it can only ever DROP an
# attribution: `D == T`, or D is in T's transitive in-project `imports`
# closure.  Within one session it filters nothing — everything there sees
# everything the session declares — and over a corpus it is the difference
# between "some theory somewhere spells this name" and "this proof could
# possibly mean that lemma".
REACH_MODES = ("closure", "name")


class _Visibility:
    r"""Which theories' declarations each theory can name, computed lazily.

    One closure at a time, not all of them: over a whole corpus the closures
    are large and overlapping, so materialising 9,600 of them costs far more
    memory than the sections do — and every scan that needs this walks the
    sections in order anyway, so a per-theory cache is used once and then
    never again.  The `imports` ADJACENCY is memoised instead, which is the
    part that costs I/O: `parse_thy_imports` re-reads a theory file on every
    call, so without this a per-theory BFS would re-read the whole corpus once
    per theory.

    ``mode="name"`` disables the filter entirely (`sees` is always true) — the
    compatibility switch, so a corpus-scale delta can be measured against the
    numbers it replaces rather than merely asserted.

    **An unreadable header means "unknown", never "imports nothing".**  The
    rule is a necessary condition on visibility, so it may only drop an
    attribution where it is confident; a theory whose `imports` clause cannot
    be re-read (a section parsed from a buffer, the `-` stdin route, a path
    that has since moved) has an unknown closure, and the honest answer is that
    it sees everything.  Degrading the other way would delete real edges, which
    is the failure this filter exists to avoid making.
    """

    def __init__(self, sections: list[TheorySection], mode: str = "closure",
                 *, bound_names: bool = False):
        self.mode = mode
        self.by_theory = _sections_by_theory(sections)
        self._leaf = _leaf_index(self.by_theory)
        # theory -> EVERY section of that name, not the last-wins one.  A
        # name is unique in a session and not in a corpus (461 AFP names are
        # shared by 1,219 theories), and this filter may only DROP, so the
        # adjacency has to be the UNION: too large a closure is merely weak,
        # while one section's imports standing for another's deletes real
        # citations [visibility-by-name].
        self._sections_of: dict[str, list[TheorySection]] = {}
        for sec in sections:
            self._sections_of.setdefault(sec.theory, []).append(sec)
        self._closure: tuple[str, frozenset[str] | None] | None = None
        # theory -> its in-project imports, read once; None = could not read.
        self._imports: dict[str, list[str] | None] = {}
        # name -> the theories declaring it.  A name declared NOWHERE is never
        # filtered: `sees` is asked about tokens the caller already believes
        # are citable, and inventing an answer for one the project does not
        # declare would drop a real use.
        #
        # With ``bound_names``, the names an entry BINDS count as declarations
        # too [bound-name-reach]: a datatype constructor, a `shows` conjunct, a
        # mutually declared constant.  Isabelle binds `Bar` in the theory that
        # writes `datatype colour = Bar | Baz`, and a theory that does not
        # import it cannot write that `Bar` either — so a single-name scan
        # (`callers Bar`, and the site verbs) scopes it like any entry.  Off by
        # default because the bulk call graph has no such nodes: its name set
        # is entries only, and giving its visibility a wider declared set than
        # its node set would change nothing it reports while costing a pass.
        self.declared_in: dict[str, set[str]] = {}
        for sec in sections:
            for e in sec.entries:
                self.declared_in.setdefault(e.name, set()).add(sec.theory)
                if bound_names:
                    for n in e.bound_names:
                        self.declared_in.setdefault(n, set()).add(sec.theory)

    def _read_imports(self, theory: str) -> list[str] | None:
        """The in-project imports of EVERY section of this name, unioned, or
        None if any of them cannot be read.

        Unknown wins over a partial union for the reason the class exists: a
        union missing one section's imports is a closure that is too SMALL,
        and a closure that is too small drops attributions.
        """
        if theory in self._imports:
            return self._imports[theory]
        secs = self._sections_of.get(theory, ())
        got: list[str] | None
        # The readability test has to happen HERE: `parse_thy_imports` returns
        # `[]` for a file that does not exist, so through it "imports nothing"
        # and "cannot be read" are the same answer — and they must not be, or a
        # section parsed from a buffer would silently lose every cross-theory
        # edge it has.
        if not secs or any(not s.path.is_file() for s in secs):
            got = None
        else:
            names: set[str] = set()
            for sec in secs:
                for imp in parse_thy_imports(sec.path):
                    names.update(_import_candidates(imp, self.by_theory,
                                                    self._leaf))
            got = sorted(names)
        self._imports[theory] = got
        return got

    def closure(self, theory: str) -> frozenset[str] | None:
        """``{theory} | its transitive in-project imports``, or None if any
        header on the walk could not be read — see the class docstring."""
        if self._closure is not None and self._closure[0] == theory:
            return self._closure[1]
        unknown = False

        def children(name: str) -> list[str]:
            nonlocal unknown
            got = self._read_imports(name)
            if got is None:
                unknown = True
                return []
            return got

        depths = _bfs_depths(children, [theory], seed_depth=-1)
        reach = None if unknown else frozenset(depths) | {theory}
        self._closure = (theory, reach)
        return reach

    def sees(self, theory: str, name: str) -> bool:
        """May a site in ``theory`` be naming the project's ``name``?"""
        if self.mode != "closure":
            return True
        decl = self.declared_in.get(name)
        if not decl:
            return True                 # declared nowhere: nothing to scope to
        if theory in decl:
            return True                 # the fast path, and the common one
        reach = self.closure(theory)
        if reach is None:
            return True                 # unknown closure: do not drop an edge
        return not decl.isdisjoint(reach)


def site_filter(sections: list[TheorySection], name: str,
                reach: str = "closure") -> Callable[[str], bool]:
    """Which theories a single-name scan may report a hit for ``name`` in.

    The per-theory predicate behind `callers`, `instances` and `codeqs`: the
    :class:`_Visibility` rule with bound names counted as declarations
    [bound-name-reach], packaged as ``admits(theory) -> bool`` so a scan can
    test a whole section once and skip it before touching its source.

    Always true under ``reach="name"``, and equally when the project declares
    ``name`` NOWHERE — a token this project does not declare is a mention of
    something external, which no import closure has an opinion about.  That
    undeclared case is decided BEFORE any closure is built, and the ordering
    is the difference between a cheap verb and an expensive one: building a
    closure reads theory headers, and `callers <some token>` on a word the
    project never declares needs none of it.
    """
    if reach != "closure":
        return lambda theory: True
    declared = False
    for sec in sections:
        for e in sec.entries:
            if e.name == name or name in e.bound_names:
                declared = True
                break
        if declared:
            break
    if not declared:
        return lambda theory: True
    vis = _Visibility(sections, reach, bound_names=True)
    return lambda theory: vis.sees(theory, name)


def _build_call_graph(sections: list[TheorySection],
                      drop_upto: int = _DROP_NAMES_UPTO,
                      derived: bool = False,
                      reach: str = "closure") -> CallGraph:
    """Single-pass scan building a full name-level call graph.

    Uses the shared filtering helpers (`_noise_ranges`,
    `_build_def_sites`): skips text/comment blocks, definition sites, and
    antiquotation-only mentions.  ``drop_upto`` is forwarded to
    :func:`_is_citation_name` — length-1 names (variable collisions) are
    excluded by default; see that function and ``--drop-names-upto``.

    ``derived`` treats Isabelle's definitional spellings (``foo_def``,
    ``foo_defs``) as citations of ``foo``.  Off by default, because the graph is
    over FACTS and ``foo_def`` is a different fact from ``foo``; only
    :func:`commands.cmd_unused` turns it on, where the question is whether the
    DECLARATION is dead.  See the note there.

    ``reach`` scopes attribution by VISIBILITY (:class:`_Visibility`): a
    citation is attributed only to declarations the citing theory can actually
    see.  ``"name"`` restores name-only matching.  The default is what the CLI
    uses, deliberately — a library caller that got a different graph from the
    one `query` prints would be the `trivial_frac` mistake again.
    """
    # 1. Collect candidate names.  A name too short to tell from a term
    #    variable, or a bare numeral, is not a citable fact, so the universal
    #    variable `x` mints no edges.
    #
    #    A name that is ALSO a proof method / attribute / keyword is admitted,
    #    but into `shadowed`: its mentions are checked positionally below.  It
    #    used to be dropped outright, which stopped `by simp` minting edges to a
    #    `definition simp` — but also erased every genuine citation of any entry
    #    whose name collides with the bound table.  The table is a union over
    #    sessions, and `HOL-Eisbach` exports the methods of its own `Tests`
    #    theory, so `lemma foo` disappeared from `callers` and `unused`
    #    entirely.  Position tells the two apart; a name never can.
    name_set: set[str] = set()
    shadowed: set[str] = set()
    for sec in sections:
        for e in sec.entries:
            if (e.tag in _CITABLE_TAGS and e.name != "?"
                    and len(e.name) > drop_upto and not e.name.isdigit()):
                name_set.add(e.name)
                if e.name in _NON_CITATION:
                    shadowed.add(e.name)

    # 1b. Derived-fact spellings.  Isabelle mints `foo_def` from `definition
    #     foo`, and citing it IS a use of `foo` — often the only one, since an
    #     `equal` instance proof cites nothing but `equal_foo_def`.  The dotted
    #     families (`foo.simps`, `foo.induct`) need no help: the `[\w']+`
    #     tokeniser already splits them, leaving a bare `foo` to match.  The
    #     underscore family does not split, so map it back explicitly.  An entry
    #     genuinely named `foo_def` keeps its own identity — only spellings that
    #     are not themselves entries are treated as derived.
    derived_base: dict[str, str] = {}
    for n in (name_set if derived else ()):
        for suffix in ("_def", "_defs"):
            spelling = n + suffix
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
    #
    #    word_re is run over the SYMBOL-BLANKED line, not the raw one
    #    [symbol-body-tokens].  A `\<...>` token's body is the symbol's own
    #    name, never a fact's, but `[\w']+` reaches straight into it:
    #    `\<lambda>` yields `lambda`, `\<le>` yields `le`, `\<^sub>` yields
    #    `sub` — and the AFP declares 7 entries named `lambda`, 37 named `le`
    #    and 27 named `sub`, so every `\<lambda>` in the corpus cited all
    #    seven.  Blanking loses nothing the pass is for: `iso_transaction` in
    #    `iso_transaction\<^sub>h` is still a maximal run, and the symbolic
    #    spelling is sym_re's job.
    sym_re = re.compile(rf"{ISA_WORD_CHAR}+")
    sym_token_re = re.compile(ISA_SYMBOL)
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
    sym_blank = sym_token_re.sub
    quoted_findall = quoted_re.findall

    vis = _Visibility(sections, reach)
    for sec in sections:
        # The redacted view (`live_source`), not the raw source: a comment, an
        # `\<^cancel>` region or an inline ML body that SHARES its line with
        # live proof text is blanked in place, so `by simp (* see foo *)` stops
        # citing `foo`.  Nothing else in this loop changes — the redaction
        # preserves every line and column, so the mask below and the 1-indexed
        # arithmetic still address the same characters.
        lines = sec.live_source()
        t_ranges = text_ranges.get(sec.path, [])
        d_map = def_sites.get(sec.path, {})
        idx = line_index.get(sec.path, [])
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
            # A `\<...>` token's body is the symbol's name, not a fact's, so
            # the word pass reads the line with those tokens blanked.  Only
            # lines that carry one pay the substitution.
            words = word_findall(
                sym_blank(" ", stripped) if "\\<" in stripped else stripped)
            cand = ns_inter(words)
            # `foo_def` resolves to `foo` (see derived_base).  Guarded on the map
            # being non-empty so the default path pays a truthiness test rather
            # than a set intersection on every line of every theory.
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
            # A candidate whose name is also a method/attribute has to earn its
            # edge positionally.  Guarded so the ordinary line pays one set
            # intersection, not the re-read.
            if shadowed:
                sh = cand & shadowed
                if sh:
                    cand = (cand - sh) | _shadowed_uses_on_line(line, sh, derived)
                    if not cand:
                        continue
            caller_entry = _entry_at_line(idx, line_no)
            if caller_entry is not None and caller_entry.name == "?":
                continue
            # A citation outside every indexed entry is still a real use: the
            # span-bounding outer commands (`instance`, `lemmas`, `declare`,
            # `code_printing`, `export_code`) cite facts but declare nothing, so
            # they own no lines.  Dropping their citations makes the cited fact
            # read as unused — an `equal` instance proof is the whole reason its
            # own `equal_*` definition exists.  Attribute them to a synthetic
            # per-theory top-level caller so the edge exists and carries a place.
            caller_name = (caller_entry.name if caller_entry is not None
                           else f"{sec.theory}:<toplevel>")
            for name in cand:
                d_ranges = d_map.get(name)
                if d_ranges and any(line_no in r for r in d_ranges):
                    continue
                # Visibility, asked per CANDIDATE rather than per name in the
                # index: `cand` holds the handful of names actually on this
                # line, where `name_set` holds every name in the corpus.  The
                # closure is cached for the theory being scanned, so the walk
                # is paid once per theory and this is a set test.
                if not vis.sees(sec.theory, name):
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
                  ) -> tuple[Counter, list[tuple[Path, int, "Entry | None", str]]]:
    """Tally proof-method uses across live theory source.

    Returns ``(counts, located)``:

    * ``counts`` — :class:`collections.Counter` ``{method: occurrences}`` over
      every ``by`` / ``apply`` / ``proof`` introducer on a *live* line (not a
      ``text \\<open>...\\<close>`` block, a ``\\<comment>`` annotation, or a
      per-entry preamble — so prose like "apply the rule" is not mined).
    * ``located`` — ``[(path, line_no, owning_entry, line_text)]`` for the
      method named by ``only`` (empty when ``only`` is None), the method
      analogue of :func:`_find_callers`.  The section's PATH rather than its
      theory name, because 461 AFP theory names are shared and the printed
      locus has to name one theory; `render.locus_labels` turns it into the
      label, which is a layer this module sits below [disambig-loci].

    The tally is **positional**, not table-filtered: whatever sits in introducer
    position is the method, exactly as :func:`_leading_method` classifies a
    step's discharge — that docstring carries the reasoning.  Requiring table
    membership here made this verb under-report every tactic an entry defines for
    itself, which is the kind a reader most needs to find.

    This is the complement of the citation router, and now structurally so: the
    first token after ``by``/``apply`` is what ``_cited_facts_on_line`` consumes
    as the method rather than as a fact, so the two scans partition an introducer
    line between them by position, with no table mediating the split.
    """
    counts: Counter = Counter()
    located: list[tuple[Path, int, Entry | None, str]] = []
    line_index = _build_line_index(sections)
    intro_finditer = _METHOD_INTRO_RE.finditer
    for sec in sections:
        # Scan the redacted view, report the real one: `by simp (* or apply
        # auto *)` must not count `auto` as a method use, but the located hit
        # has to show the user their actual line, blanks included nowhere.
        lines = sec.live_source()
        raw = sec.source()
        # "Live" = not inside a text block, multi-line \<comment>, or preamble
        # (the same notion `_grep_sections` uses), so an `apply`/`by` mentioned
        # in prose does not register as a method use.  A 1-indexed line mask
        # gives O(1) liveness per line, vs rescanning every noise range (the
        # same flattening the call-graph build uses).
        noise_mask = _line_mask(len(lines), _noise_spans(sec))
        idx = line_index.get(sec.path, [])
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
                counts[tok] += 1
                if tok == only:
                    hit_only = True
            if hit_only:
                located.append((sec.path, line_no,
                                _entry_at_line(idx, line_no),
                                raw[line_no_0].rstrip()))
    return counts, located


def _leading_method(line: str) -> str:
    """The first proof method named on ``line`` — the token after a ``by`` /
    ``apply`` / ``proof`` introducer.

    Purely **positional**: in introducer position the token *is* the method, so
    it is not checked against the bound ``PROOF_METHODS`` table.  That check used
    to be here, and it made this the one shape axis whose denominator depended on
    configuration — an entry's own Eisbach or ML tactic (`cs_concl`,
    `parametricity`, `urule`) left ``Step.method`` empty, and since that is
    :func:`shape.trivial_frac`'s denominator, the step did not go unclassified,
    it left the measure.  No fixed table can carry a tactic an entry defines for
    itself, so the table was not narrow, it was the wrong instrument.

    Dropping it also makes this agree with ``_cited_facts_on_line``, which has
    always read the first token after ``by``/``apply`` as the method by position
    with no table lookup.  The two scans are meant to partition a proof line
    between methods and citations; while this one consulted a table and that one
    did not, they could not.

    Returns ``""`` when the line introduces no method at all (``by (rule r)`` ->
    ``"rule"``; ``qed`` / a bare ``.`` / ``proof -`` -> ``""``, since ``[\\w']+``
    matches no token there).  Line-anchored like the width scanner: a method
    wrapped onto a continuation line is not seen (undercount, never overcount).
    """
    for m in _METHOD_INTRO_RE.finditer(line):
        return m.group(1)
    return ""


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
# Isar command keyword families and positional fact-citation extraction
# ---------------------------------------------------------------------------
#
# The call graph above answers "which entries MENTION name X" — position-blind:
# a name in a statement `"foo = foo"` counts as much as one in `using foo`.
# A different, narrower question is "which facts does this proof step CITE" —
# the arguments of `from`/`using`/`with`/`unfolding` and of the closing method.
# `_cited_facts_on_line` is the shared home for that positional notion: the
# width fan-in metric (M5a) aggregates it per step, and a future per-step
# `callers` view can reuse it.  It is deliberately conservative — it counts only
# high-confidence fact positions and flags any method shape it cannot classify,
# so a census can report method-syntax coverage (M5a records `null` rather than
# guessing, and the census sums the coverage).

# The four Isar proof-command families (see the `shape` module docstring).  Defined
# here in the shared analysis layer so both the width step classifier and the
# fact extractor read one list.
GOAL_KEYWORDS = frozenset({
    "have", "show", "hence", "thus", "obtain", "consider",
    "also", "finally", "interpret",
})
CONTEXT_KEYWORDS = frozenset({
    "fix", "assume", "presume", "define", "let", "case",
})
PLUMBING_KEYWORDS = frozenset({
    "from", "using", "with", "note", "moreover", "ultimately", "then",
    "unfolding",
})
CLOSING_KEYWORDS = frozenset({
    "by", "apply", "done", "qed",
})

# Prefix/suffix fact-list keywords whose following identifiers are cited facts.
# `note` is excluded — it *introduces* a fact (`note x = ...`), it does not cite.
_CITE_LIST_WORDS = frozenset({"from", "with", "using", "unfolding"})
# A fact list runs until a goal/closing keyword (`from a have`, `using a by`) —
# or until the *next* cite keyword, so a chain (`using X unfolding Y`) ends the
# first list rather than swallowing `unfolding` as one of X's facts.
_FACT_LIST_STOP = (GOAL_KEYWORDS | CLOSING_KEYWORDS | _CITE_LIST_WORDS
                   | {"proof", "and"})

# Methods whose *bare* (colon-free) arguments are fact names, not terms/flags:
# `by (rule conjI)`, `by (metis a b)`, `by (unfold d)`.
_RULE_METHODS = frozenset({
    "rule", "erule", "drule", "frule", "intro", "elim", "dest",
    "metis", "meson", "subst", "unfold", "fold",
})
# Methods whose bare arguments are terms / flags / induction variables — never
# facts.  A bare arg here is a *covered* non-fact, not an unclassifiable token.
_TERM_ARG_METHODS = frozenset({
    "simp", "simp_all", "auto", "blast", "fastforce", "force", "fast",
    "clarsimp", "clarify", "safe", "linarith", "arith", "presburger",
    "algebra", "argo", "order", "eval", "normalization", "cases", "case_tac",
    "induct", "induction", "induct_tac", "coinduct", "coinduction",
    "standard", "rule_tac", "subgoal", "hypsubst", "-", "goal_cases",
})
# `NAME:` markers after which the trailing identifiers (until the next marker /
# structural token) are facts: `simp add: f g`, `auto simp: h`, `intro: i`.
_FACT_MARKER_WORDS = frozenset({
    "simp", "add", "del", "intro", "dest", "elim", "cong", "split",
})
# Attribute-position fact composers: the bracket attributes whose arguments are
# *facts*, not terms/flags — `r[OF a b]`, `r[THEN t]`, `d[unfolded e_def]`,
# `d[folded e_def]`, `t[simplified s]`.  Every other attribute (`of`, `where`,
# `symmetric`, `simp`, `rule_format`, ...) takes terms or is a bare flag, so it
# contributes no citation; see :func:`_consume_attr_block`.
_ATTR_FACT_WORDS = frozenset({"OF", "THEN", "unfolded", "folded", "simplified"})

# Strip quoted propositions and cartouches so their internal tokens are never
# mistaken for cited facts (`have "using x" by ...` cites nothing from the term).
_DQUOTE_STRIP_RE = re.compile(r'"[^"]*"')
_CARTOUCHE_STRIP_RE = re.compile(r"\\<open>.*?\\<close>")
# The same two regions, captured rather than blanked: the *term* text of a line.
# A name occurring here is being used as a constant or in a statement, which is
# a real use even when that name also happens to be a proof method.
_PROP_TEXT_RE = re.compile(r'"([^"]*)"|\\<open>(.*?)\\<close>')
# Token stream for the fact walk: names (with internal dots for qualified
# spellings), the `..` proof, and the structural chars that delimit method args.
# `ISA_SYMBOL`, not the narrower name atom: this is a RUN scanner over source
# the tokenizer has already redacted, so its job is to find where a token ends.
# Narrowing it would split a stray `\<open>foo` and offer `open` as a candidate
# fact — inventing an edge, which is the one thing this walk must not do.
_FACT_TOK_RE = re.compile(
    rf"\.\.|{ISA_WORD_CHAR}(?:{ISA_SYMBOL}|[\w'.])*|[():,|\[\]]|:")
# Structural tokens that never name a fact.
_STRUCTURAL = frozenset({"(", ")", "[", "]", "|", ",", ":", ".."})


def _strip_props(text: str) -> str:
    """Blank out quoted / cartouche propositions so their tokens are not read as
    cited facts."""
    text = _DQUOTE_STRIP_RE.sub(" ", text)
    return _CARTOUCHE_STRIP_RE.sub(" ", text)


def _looks_like_fact(tok: str) -> bool:
    r"""A candidate fact token is kept unless it cannot be an Isabelle fact name:
    a structural token, the lone wildcard ``_``, or a token that does not begin
    like an identifier — one led by a digit or a prime.

    An Isabelle long-identifier starts with a letter, an underscore, or a symbol
    token (`\<phi>_def`), never a digit or a `'`.  So a digit-led token is a
    numeral or a statement-text artifact (`31`, `0..`, `1.`, a glued `33have`
    from a spacing quirk), and a prime-led token is a type variable (`'a`) — both
    are terms/labels, not cited facts, and idf would otherwise weight such a
    df-1 artifact maximally.  Symbol-led names (`\<phi>_def`) and short labels
    (`a`, an `assumes a:`; `le`, a rule) are kept: unlike the position-*blind*
    citation graph, this extractor only inspects fact-argument positions, so a
    single-char token there *is* a fact and no length floor applies.  The bare
    ``_`` is the term placeholder (`rule r[OF _ h]`), never a fact."""
    return (tok != "_" and tok not in _STRUCTURAL
            and not tok[:1].isdigit() and not tok.startswith("'"))


def _consume_attr_block(toks: list[str], i: int, facts: set[str]) -> int:
    r"""Consume a postfix attribute block — ``toks[i]`` is the opening ``[`` —
    adding to ``facts`` only the arguments of the *fact-composing* attributes
    (:data:`_ATTR_FACT_WORDS`: ``OF`` / ``THEN`` / ``unfolded`` / ``folded`` /
    ``simplified``).  A term- or flag-valued attribute (``of``, ``where``,
    ``symmetric``, a bare declaration) contributes nothing, so its inner tokens
    — bound variables, ``\<phi>``, ``and``, numerals — no longer leak as facts.

    Returns the index just past the matching ``]``.  Nested brackets are tracked
    by depth; a comma resets to the next attribute head; a ``NAME:`` sub-marker
    (``[simplified add: f]``) is skipped so the marker word is not itself read as
    a fact.
    """
    n = len(toks)
    depth = 0
    take = False                     # inside a fact-composing attribute
    while i < n:
        t = toks[i]
        if t == "[":
            depth += 1
            take = False
        elif t == "]":
            depth -= 1
            take = False
            if depth == 0:
                return i + 1
        elif t in _ATTR_FACT_WORDS:
            take = True
        elif t == ",":
            take = False             # a fresh attribute head follows
        elif take and _looks_like_fact(t) \
                and not (i + 1 < n and toks[i + 1] == ":"):
            facts.add(t)
        i += 1
    return i                         # unbalanced — consumed to end of line


def _cited_facts_on_line(line: str) -> tuple[set[str], bool]:
    r"""Fact names cited in the citation positions of one proof line, plus a
    ``covered`` flag.

    Extracts the arguments of ``from`` / ``with`` / ``using`` / ``unfolding``,
    the ``NAME:``-marked fact lists inside a method (``simp add: f g``), the bare
    arguments of a rule-style method (``rule r``, ``metis a b``), and the
    fact-composing attribute blocks (``[OF a]`` / ``[THEN t]`` /
    ``[unfolded d]``).  Quoted propositions are stripped first, so a term that
    merely *contains* a keyword is ignored.

    Two shapes that used to leak spurious tokens are handled exactly:
    a **chained cite keyword** (``using X unfolding Y``) ends the first fact
    list rather than being read as one of ``X``'s facts; and a
    **term-/flag-valued attribute** (``[of t]``, ``[where x=t]``,
    ``[symmetric]``) contributes nothing, so its inner terms — bound variables,
    ``\<phi>``, ``and`` — are not mistaken for cited facts (:func:`_consume_attr_block`).

    ``covered`` is ``False`` when the line applies a method that is neither a
    known rule-method nor a known term-arg method *and* passes bare arguments —
    i.e. a shape whose arguments cannot be classified as facts-or-not.  The
    census sums this into a method-syntax coverage statistic.
    """
    toks = _FACT_TOK_RE.findall(_strip_props(line))
    facts: set[str] = set()
    covered = True
    i, n = 0, len(toks)
    in_method = False       # inside a `by`/`apply` method expression
    cur_method: str | None = None
    while i < n:
        t = toks[i]
        # from / with / using / unfolding fact list (prefix or suffix).  Each
        # listed fact may carry its own attribute block (`using assms[OF x]`),
        # whose OF/THEN premises join the list; a chained cite keyword or a
        # goal/closing keyword ends it.
        if t in _CITE_LIST_WORDS:
            j = i + 1
            while j < n and toks[j] not in _FACT_LIST_STOP:
                tj = toks[j]
                if tj == "[":
                    j = _consume_attr_block(toks, j, facts)
                    continue
                if tj in _STRUCTURAL:
                    break
                if _looks_like_fact(tj):
                    facts.add(tj)
                j += 1
            i = j
            continue
        if t in ("by", "apply"):
            in_method = True
            cur_method = None
            i += 1
            continue
        if in_method:
            # A postfix attribute block on the preceding fact/method: only its
            # OF/THEN/unfolded/... arguments cite; `[of t]`/`[where x=t]` do not.
            if t == "[":
                i = _consume_attr_block(toks, i, facts)
                continue
            # A method marker `NAME:` — trailing tokens are facts, until the
            # next marker, a method-group close/separator, or a closing keyword.
            if t in _FACT_MARKER_WORDS and i + 1 < n and toks[i + 1] == ":":
                j = i + 2
                while j < n:
                    tj = toks[j]
                    # Any modifier keyword begins a new group and ends this fact
                    # list — including the two-word `simp add:` / `simp del:`
                    # form, where `simp` is not itself followed by `:`.
                    if tj in _FACT_MARKER_WORDS:
                        break
                    if tj in CLOSING_KEYWORDS or tj in (")", "]", "|", ","):
                        break                       # group close / separator
                    if tj == "[":
                        j = _consume_attr_block(toks, j, facts)
                        continue
                    if _looks_like_fact(tj):
                        facts.add(tj)
                    j += 1
                i = j
                continue
            if t in _STRUCTURAL:
                if t in ("(", ")", "|", ","):
                    cur_method = None   # a fresh method head may follow
                i += 1
                continue
            if cur_method is None:
                cur_method = t          # the method name
                i += 1
                continue
            # A bare argument to the current method.
            if cur_method in _RULE_METHODS:
                if _looks_like_fact(t):
                    facts.add(t)
            elif cur_method in _TERM_ARG_METHODS:
                pass                    # a term / flag, not a fact
            else:
                covered = False         # unknown method with bare args
            i += 1
            continue
        i += 1
    return facts, covered
