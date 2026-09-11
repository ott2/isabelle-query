"""Corpus-scale robustness checks — skipped unless ``ISABELLE_QUERY_CORPUS``
points at a directory tree of ``.thy`` files (e.g. an AFP checkout).
These are the "intricate" tests: they re-run the full-tree
measurements that motivated the parser and call-graph work.

    ISABELLE_QUERY_CORPUS=/path/to/afp/thys python -m unittest tests.test_corpus

They are intentionally not part of the default run, since the corpus is large
and not vendored into this repository.
"""

import glob
import os
import re
import sys
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from support import cli, brute_force_call_graph  # noqa: E402

CORPUS = os.environ.get("ISABELLE_QUERY_CORPUS")

# Keep the slow oracle comparison to a bounded slice of the corpus.
_ORACLE_SUBSET = 120
# Allowed share of caller-edges the fast builder may drop vs the reference.
# The fast builder never *invents* an edge (asserted separately); it may drop
# a tiny fraction where the per-name reference over-matches a short symbolic
# name inside a longer identifier (e.g. `\<gamma>` within `\<gamma>\<^sub>1`) —
# a spurious reference hit the token model correctly ignores.
#
# Measured at exactly ONE edge over the 120-file subset
# (`AOT_model:<toplevel> -> AOT_urrel_\<omega>equiv`, precisely that symbolic
# over-match), so the ceiling has three orders of magnitude of headroom.  It is
# a ceiling rather than an equality because the corpus moves; if it is ever
# approached, `scripts/probe_oracle_drop.py` separates the populations before
# anyone reaches for the number.
_MAX_DROP_FRACTION = 0.005
# Robustness target: the `?` (unparsed-name) rate.  The bulk of the residual
# is genuinely-anonymous lemmas (`lemma "P"`, `lemma [simp]:`) and nameless
# custom commands (a `C` C-code block, an `autocorres`/`synthesize` tool
# invocation), which are *correctly* nameless; the recoverable corner cases
# are catalogued as expected-failures in tests/test_known_failures.py.
_MAX_UNPARSED_FRACTION = 0.07
# A leaked `(in locale)` modifier would appear verbatim at the start of a name.
_LOCALE_LEAK_RE = re.compile(r"\(in\s")
# Ceiling on entries whose recorded body runs PAST their own span
# (`body_end_line > thy_end`), i.e. one declaration's body overlapping the
# next.  `compute_spans` sets `thy_end` from the following entry's
# `src_start`, so an overlap means a `show`/`enclosing`/relocation cut reaches
# into a neighbour.
#
# Measured at 82 over the AFP.  It is a CEILING rather than an equality
# because the residual is a real (small, unfixed) tail and the corpus moves;
# the point is that it must not grow.  This is the check that rejected the
# wider `[decl-body-comment]` fix, which repaired 5 truncated declarations and
# took this number to 719 — a trade invisible to the entry-set diff, which
# only reported "more records changed".
_MAX_SPAN_OVERLAP = 120


@unittest.skipUnless(CORPUS and os.path.isdir(CORPUS),
                     "set ISABELLE_QUERY_CORPUS to a .thy tree to run corpus tests")
class Corpus(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.files = sorted(glob.glob(os.path.join(CORPUS, "**", "*.thy"),
                                     recursive=True))
        if not cls.files:
            raise unittest.SkipTest(f"no .thy files under {CORPUS}")
        # Mirror load_index: build the active root's custom-command union from
        # every header, so the measurements below reflect the real parse (a
        # theory that *uses* a command another *declares* is recognised).  We
        # set the module global rather than threading a param so the oracle
        # test's cli._parse_one sees it too.
        cli._CUSTOM_COMMANDS.clear()
        cli._populate_custom_commands([(Path(p).stem, Path(p))
                                       for p in cls.files])

    @classmethod
    def tearDownClass(cls):
        cli._CUSTOM_COMMANDS.clear()  # don't leak the union into other tests

    def _iter_entries(self, paths):
        for p in paths:
            try:
                with open(p, encoding="utf-8", errors="replace") as fh:
                    lines = fh.read().splitlines()
            except OSError:
                continue
            yield p, cli.extract_entries(lines)

    def test_unparsed_name_rate_is_low(self):
        total = unparsed = 0
        for _p, entries in self._iter_entries(self.files):
            for e in entries:
                total += 1
                if e.name == "?":
                    unparsed += 1
        self.assertGreater(total, 0)
        frac = unparsed / total
        self.assertLess(
            frac, _MAX_UNPARSED_FRACTION,
            f"unparsed-name rate {frac:.2%} exceeds {_MAX_UNPARSED_FRACTION:.0%} "
            f"({unparsed:,}/{total:,})")

    def test_bodies_stay_inside_their_own_spans(self):
        # Full sections, not `_iter_entries`: that calls `extract_entries`
        # alone, and `thy_end` is set later by `compute_spans`, so the
        # comparison would be against 0 for every entry and pass vacuously.
        over = []
        for p in self.files:
            try:
                sec = cli._parse_one(Path(p).stem, Path(p))
            except Exception:  # noqa: BLE001 — a corpus has unparseable files
                continue
            for e in sec.entries:
                if e.thy_end and e.body_end_line > e.thy_end:
                    over.append(f"{sec.theory}:{e.thy_line} {e.name} "
                                f"body_end={e.body_end_line} > "
                                f"thy_end={e.thy_end}")
        self.assertLess(
            len(over), _MAX_SPAN_OVERLAP,
            f"{len(over)} entries whose body runs past their own span "
            f"(ceiling {_MAX_SPAN_OVERLAP}); first few: {over[:5]}")

    def test_no_locale_prefix_leaks(self):
        # the `(in locale)` qualifier must never end up *in* the parsed name.
        # (A double-quoted name may legitimately start with '(', e.g.
        # "(inv upOne) n = n - 1", so match the leak pattern, not just '('.)
        for _p, entries in self._iter_entries(self.files):
            for e in entries:
                if e.name != "?":
                    self.assertIsNone(
                        _LOCALE_LEAK_RE.match(e.name),
                        f"locale prefix leaked into name {e.name!r} in {_p}")

    def test_custom_commands_bound_aot_spans(self):
        # Regression for the reported `largest`/`show` bug: AOT's `AOT_theorem`
        # commands, unrecognised, let the built-in `theorem "beta-C-cor:3"`
        # swallow the whole run after it (a 3867-line span).  With the scanner
        # the surrounding AOT_theorems bound it to its real ~7-line proof.
        aot = [p for p in self.files if p.replace(os.sep, "/").endswith(
            "AOT/AOT_PLM.thy")]
        if not aot:
            self.skipTest("AOT_PLM.thy not in this corpus")
        sec = cli._parse_one("AOT_PLM", Path(aot[0]))
        target = [e for e in sec.entries if e.name == "beta-C-cor:3"]
        self.assertEqual(len(target), 1, "beta-C-cor:3 should be a single entry")
        span = target[0].thy_end - target[0].thy_line + 1
        self.assertLess(span, 50, f"beta-C-cor:3 span {span} lines not collapsed")
        # The AOT_theorem facts around it must now be indexed by their labels.
        by_name = {e.name for e in sec.entries}
        self.assertIn("beta-C-cor:1", by_name)  # an AOT_theorem (thy_goal)

    def _subset_sections(self):
        return [cli._parse_one(Path(p).stem, Path(p))
                for p in self.files[:_ORACLE_SUBSET]]

    def test_fast_call_graph_matches_oracle_on_subset(self):
        secs = self._subset_sections()
        # `reach="name"`, NOT the shipped default.  The reference implements
        # query's tokenisation and attribution rules; it has no visibility
        # filter at all, so comparing it against the default `"closure"`
        # measures the REACH rule rather than a builder divergence — which is
        # what this assertion spent a fortnight reporting as one: 504 of the
        # 505 edges were `[citation-reach]` working exactly as designed, and
        # the true residual was a single edge [oracle-drop-rate].  The reach
        # rule has its own pin, immediately below and in test_citation_reach.py.
        fast = cli._build_call_graph(secs, reach="name")
        ref = brute_force_call_graph(secs)

        # The fast builder must never invent an edge the reference lacks.
        for name, callers in fast.callers.items():
            self.assertLessEqual(
                callers, ref.callers.get(name, set()),
                f"fast builder invented callers for {name!r}")

        # It may drop only a tiny, bounded number of true edges.
        total = sum(len(v) for v in ref.callers.values())
        dropped = sum(len(ref.callers[n] - fast.callers.get(n, set()))
                      for n in ref.callers)
        self.assertLessEqual(
            dropped, max(2, int(total * _MAX_DROP_FRACTION)),
            f"fast builder dropped {dropped}/{total} caller-edges")

    def test_reach_scoping_only_drops_edges(self):
        """`TheRuleOnlyDrops` at corpus scale.

        Pinning the differential at `reach="name"` above would otherwise leave
        the SHIPPED default untested here.  `test_citation_reach.py` pins this
        invariant on a hand-built fixture; this runs it against real `imports`
        clauses, which is the only place `_Visibility` actually reads — and the
        subset spans 7 AFP entries, so the closures are genuinely partial.
        """
        secs = self._subset_sections()

        def edges(g):
            return {(c, n) for n, cs in g.callers.items() for c in cs}

        closure = edges(cli._build_call_graph(secs, reach="closure"))
        by_name = edges(cli._build_call_graph(secs, reach="name"))
        invented = closure - by_name
        self.assertFalse(
            invented,
            f"reach scoping INVENTED {len(invented)} edges; it may only drop. "
            f"First few: {sorted(invented)[:5]}")
        # Not vacuous: over this subset the rule drops ~500 of ~10,900.
        self.assertTrue(by_name - closure,
                        "reach scoping dropped nothing — the subset no longer "
                        "exercises the filter, so the subset check is vacuous")


if __name__ == "__main__":
    unittest.main()
