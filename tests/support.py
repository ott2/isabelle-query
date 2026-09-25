"""Shared helpers for the isabelle-query test suite.

Importing this module puts the ``src/`` layout on ``sys.path`` so the tests
run against the working tree without an editable install, and exposes small
fixture builders plus a brute-force call-graph REFERENCE BUILDER.

:func:`brute_force_call_graph` is the deliberately-obvious O(lines x names)
reference implementation: for every source line it tests every indexed name
with the prime-aware boundary regex.  The shipped ``cli._build_call_graph`` is
a linear-time rewrite of the same thing, so pinning it to the reference on
fixtures guards against the fast path silently drifting from the
slow-but-clearly-correct one.

**It is not an oracle, and that word is avoided here deliberately.**  It is a
*differential* check between two implementations of query's own rules, and it
shares its exclusion helpers with the thing it checks: ``cli._noise_ranges``,
``_build_def_sites`` and ``_is_citation_name`` are called by both sides.  So
for the exclusion set itself the two inherit the same membership — change what
counts as live source and parity keeps holding while real output moves.  That
is how the call graph's missing formal-comment skip stayed hidden for as long
as it did, and it is why a change there needs its own fixture rather than a
green parity run.

Ground truth about *Isabelle* comes from Isabelle, and has never lived in this
file: see ``scripts/probe_pide_markup.py`` and ``probe_export_oracle.py``.
Two different claims, one word — this docstring exists so the two do not get
confused again.
"""

import functools
import os
import re
import sys
import tempfile
import unittest
from pathlib import Path

_SRC = Path(__file__).resolve().parent.parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from isabelle_query import cli  # noqa: E402
from isabelle_query import _namespace_resolve as _nsr  # noqa: E402
from isabelle_query import graph  # noqa: E402
from isabelle_query.parsing import _balanced_end  # noqa: E402


# The import-time default is the BROAD committed union, which already carries
# auto / blast / induct (see `graph`'s namespace block) — so most tests about HOL
# method recognition need no help.  `needs_hol_methods` is for the stricter claim:
# validate against a *session-exact* table dumped from a running Isabelle, so a
# test pinning method semantics is checked against the prover rather than against
# our own committed approximation of it.  Skipped — never failed — when Isabelle
# cannot supply one, so the suite stays green on a bare no-Isabelle CI.
_HOL_TABLE_CACHE: list = []


def _hol_table():
    """The HOL method/attribute table from Isabelle, or ``None`` if unavailable.
    Resolved at most once per process (``auto``'s presence distinguishes a real
    HOL dump from the Pure fallback)."""
    if not _HOL_TABLE_CACHE:
        r = _nsr.resolve_namespace("HOL")
        _HOL_TABLE_CACHE.append(r if "auto" in r["methods"] else None)
    return _HOL_TABLE_CACHE[0]


def needs_hol_methods(test_fn):
    """Bind the **session-exact** HOL proof-method table dumped from a running
    Isabelle for the wrapped test (restoring the previous table after), or
    ``skipTest`` when Isabelle cannot supply one.

    For the handful of tests whose claim is about HOL's method semantics rather
    than about our scanning: they are checked against the prover's own table, not
    the committed union that would otherwise answer them."""
    @functools.wraps(test_fn)
    def wrapper(self, *args, **kwargs):
        table = _hol_table()
        if table is None:
            self.skipTest("session-exact HOL proof-method table unavailable — "
                          "no Isabelle / no built HOL heap")
        saved = (graph._PROOF_METHODS, graph._ATTRIBUTES, graph._KEYWORDS)
        self.addCleanup(lambda: graph.configure_namespace(*saved))
        graph.configure_namespace(table["methods"], table["attributes"],
                                  graph._KEYWORDS)
        return test_fn(self, *args, **kwargs)
    return wrapper


def section_from(snippet, theory="Test"):
    """Parse a theory snippet (str) into a fully-populated TheorySection,
    exactly as ``load_index`` would (spans, comments, body extents)."""
    with tempfile.NamedTemporaryFile("w", suffix=".thy", delete=False,
                                     encoding="utf-8") as fh:
        fh.write(snippet)
        path = fh.name
    try:
        sec = cli._parse_one(theory, Path(path))
        sec.source()  # populate the lazy source cache before the file is removed
        return sec
    finally:
        os.unlink(path)


def sections_from(named_snippets):
    """named_snippets: dict ``{theory_name: snippet}``.  Returns a list of
    TheorySection, preserving insertion order."""
    return [section_from(snip, name) for name, snip in named_snippets.items()]


def names(section):
    """Entry names of a section, in source order."""
    return [e.name for e in section.entries]


def tags_by_name(section):
    """Map ``{name: tag}`` for a section's entries."""
    return {e.name: e.tag for e in section.entries}


def blank_terms(s):
    r"""The outer view of a one-line header, simulated: every `"..."` term and
    `\<open>...\<close>` cartouche blanked to spaces, which is what
    `TheorySection.outer_source` does to the same characters.  For pinning
    the site grammars (`sites.expression_heads`, `sites.code_attrs`, ...) on
    strings: each takes the live text and the outer text of one span."""
    out = []
    i = 0
    quoted = False
    while i < len(s):
        c = s[i]
        if c == '"':
            quoted = not quoted
            out.append(" ")
            i += 1
        elif not quoted and s.startswith("\\<open>", i):
            e = _balanced_end(s, "\\<open>", "\\<close>", start=i)
            stop = len(s) if e < 0 else e
            out.append(" " * (stop - i))
            i = stop
        else:
            out.append(" " if quoted else c)
            i += 1
    return "".join(out)


_ANTIQ_RE = re.compile(r'@\{(?:text|thm|term|const)\s+["\']?\w+["\']?\}')


def brute_force_call_graph(sections, drop_upto=cli._DROP_NAMES_UPTO,
                           derived=False):
    """Reference O(lines x names) call-graph builder, for differential tests.

    Not an oracle — see this module's docstring for what that distinction
    costs when it is forgotten.

    Mirrors ``cli._build_call_graph`` semantics (text-block skip,
    antiquotation strip, def-site exclusion, line->entry attribution) but
    via the naive per-name boundary search rather than tokenisation.
    ``drop_upto`` is forwarded to ``cli._is_citation_name`` exactly as the
    fast builder forwards it, so the two stay in parity at any threshold.

    ``derived`` mirrors the fast builder likewise: with it set, Isabelle's
    definitional spellings (``foo_def``, ``foo_defs``) count as citations of
    ``foo`` unless that spelling is itself an indexed entry.
    """
    name_set = {e.name for s in sections for e in s.entries
                if e.tag in cli._CITABLE_TAGS and e.name != "?"
                and len(e.name) > drop_upto and not e.name.isdigit()}
    # Names that are also a proof method / attribute / keyword earn their edges
    # positionally rather than being dropped; mirrors the fast builder.
    shadowed = {n for n in name_set if n in graph._NON_CITATION}
    # Spellings searched for each name: itself, plus its derived forms.
    spellings = {n: [n] + ([s for s in (n + "_def", n + "_defs")
                            if s not in name_set] if derived else [])
                 for n in name_set}
    def_sites = cli._build_def_sites(sections, name_set)
    text_ranges = cli._noise_ranges(sections)
    line_index = cli._build_line_index(sections)
    callers = {n: set() for n in name_set}
    callees = {}
    for sec in sections:
        # Mirrors the fast builder: both read the redacted view, so a comment
        # sharing its line with proof text cites nothing in either.
        lines = sec.live_source()
        # Keyed by path, mirroring the fast builder [name-is-not-identity]:
        # a theory name is not an identity once two sections share one.
        t_ranges = text_ranges.get(sec.path, [])
        d_map = def_sites.get(sec.path, {})
        idx = line_index.get(sec.path, [])
        for i, line in enumerate(lines):
            line_no = i + 1
            if any(line_no in r for r in t_ranges):
                continue
            stripped = _ANTIQ_RE.sub("", line)
            for name in name_set:
                if not any(sp in stripped
                           and re.search(cli._isa_word_pattern(sp), stripped)
                           for sp in spellings[name]):
                    continue
                if any(line_no in r for r in d_map.get(name, set())):
                    continue
                if name in shadowed and name not in graph._shadowed_uses_on_line(
                        line, {name}, derived):
                    continue  # `by simp`, not a use of a `definition simp`
                ce = cli._entry_at_line(idx, line_no)
                if ce is not None and ce.name == "?":
                    continue
                # An entryless citation is a top-level command (`instance`,
                # `lemmas`, `export_code`): a real use with no owning entry.
                caller = ce.name if ce is not None else f"{sec.theory}:<toplevel>"
                callers[name].add(caller)
                callees.setdefault(caller, set()).add(name)
    return cli.CallGraph(callers=callers, callees=callees, all_names=name_set)
