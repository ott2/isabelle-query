"""Shared helpers for the isabelle-query test suite.

Importing this module puts the ``src/`` layout on ``sys.path`` so the tests
run against the working tree without an editable install, and exposes small
fixture builders plus a brute-force call-graph oracle.

The oracle (:func:`brute_force_call_graph`) is the deliberately-obvious
O(lines x names) reference implementation: for every source line it tests
every indexed name with the prime-aware boundary regex.  The shipped
``cli._build_call_graph`` is a linear-time rewrite of the same thing, so
pinning it to the oracle on fixtures guards against the fast path silently
drifting from the slow-but-clearly-correct one.
"""

import os
import re
import sys
import tempfile
from pathlib import Path

_SRC = Path(__file__).resolve().parent.parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from isabelle_query import cli  # noqa: E402


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


_ANTIQ_RE = re.compile(r'@\{(?:text|thm|term|const)\s+["\']?\w+["\']?\}')


def brute_force_call_graph(sections, drop_upto=cli._DROP_NAMES_UPTO,
                           derived=False):
    """Reference O(lines x names) call-graph builder used as a test oracle.

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
                if e.tag in cli._CITABLE_TAGS
                and e.name != "?" and cli._is_citation_name(e.name, drop_upto)}
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
        lines = sec.source()
        t_ranges = text_ranges.get(sec.theory, [])
        d_map = def_sites.get(sec.theory, {})
        idx = line_index.get(sec.theory, [])
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
                ce = cli._entry_at_line(idx, line_no)
                if ce is not None and ce.name == "?":
                    continue
                # An entryless citation is a top-level command (`instance`,
                # `lemmas`, `export_code`): a real use with no owning entry.
                caller = ce.name if ce is not None else f"{sec.theory}:<toplevel>"
                callers[name].add(caller)
                callees.setdefault(caller, set()).add(name)
    return cli.CallGraph(callers=callers, callees=callees, all_names=name_set)
