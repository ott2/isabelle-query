"""The subject loop: `CMD A B C` in one call [graph-once].

`_run_each` is the shared spine of the lookup verbs.  A call with several
subjects must cost what one call costs plus the per-subject work, not N times
the setup -- which for the citation verbs is the whole call graph.
"""

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, os.path.dirname(__file__))
from support import cli  # noqa: E402

from isabelle_query import commands  # noqa: E402

THY = """theory A imports Main begin
lemma base: "True" by simp
lemma mid: "True" using base by simp
lemma top: "True" using mid by simp
lemma other: "True" using base by simp
end
"""


class SubjectLoop(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        (root / "A.thy").write_text(THY)
        (root / "ROOT").write_text(
            "session S = HOL +\n  theories\n    A\n")
        self.root = str(root)
        # The committed table: no Isabelle spawn from a unit test.
        self._env = mock.patch.dict(os.environ,
                                    {"ISABELLE_QUERY_NAMESPACE": "committed"})
        self._env.start()

    def tearDown(self):
        self._env.stop()
        self._tmp.cleanup()

    def run_cli(self, *args):
        out, err = io.StringIO(), io.StringIO()
        old = sys.argv
        sys.argv = ["query", "-R", self.root, *args]
        code = 0
        try:
            with contextlib.redirect_stdout(out), \
                 contextlib.redirect_stderr(err):
                try:
                    cli.main()
                except SystemExit as e:
                    code = e.code or 0
        finally:
            sys.argv = old
        return code, out.getvalue(), err.getvalue()


class TheGraphIsBuiltOnce(SubjectLoop):

    def test_callers_r_over_three_names_builds_one_graph(self):
        real = commands._build_call_graph
        with mock.patch.object(commands, "_build_call_graph",
                               side_effect=real) as built:
            code, out, _ = self.run_cli("callers", "-r", "-c",
                                        "base", "mid", "top")
        self.assertEqual(code, 0)
        # base <- mid, other; mid <- top: so base has 3 transitive callers.
        self.assertEqual(out.split(), ["3", "1", "0"])
        self.assertEqual(built.call_count, 1)

    def test_callees_over_three_names_builds_one_graph(self):
        real = commands._build_call_graph
        with mock.patch.object(commands, "_build_call_graph",
                               side_effect=real) as built:
            self.run_cli("callees", "-c", "top", "mid", "base")
        self.assertEqual(built.call_count, 1)


class AnUnknownSubjectFailsTheBatch(SubjectLoop):
    """All or nothing [subject-batch].

    `[unresolved-subject]` made an unknown subject exit 1 with stdout
    untouched, so `$(query callees X -c)` never captures a non-answer.  The
    batch keeps that: answering the rest would leave a gap a positional reader
    cannot see -- two counts for `A bogus C`, the second of them C's.  What the
    batch gains is that EVERY unknown name is reported, not only the first.
    """

    def test_stdout_is_untouched_and_the_status_is_1(self):
        code, out, err = self.run_cli("callers", "-r", "-c",
                                      "base", "bogus", "top")
        self.assertEqual((code, out), (1, ""))
        self.assertIn("'bogus'", err)

    def test_every_unknown_subject_is_reported(self):
        code, out, err = self.run_cli("callees", "-c",
                                      "nope1", "base", "nope2")
        self.assertEqual((code, out), (1, ""))
        self.assertIn("'nope1'", err)
        self.assertIn("'nope2'", err)

    def test_a_clean_batch_matches_the_single_calls(self):
        # The blank-line layout a positional reader splits on is unchanged.
        singles = [self.run_cli("callers", "-r", n)[1]
                   for n in ("base", "mid", "top")]
        code, out, _ = self.run_cli("callers", "-r", "base", "mid", "top")
        self.assertEqual(code, 0)
        self.assertEqual(out, "\n".join(singles))

    def test_a_scan_with_no_hits_is_not_unknown(self):
        # Plain `callers` scans text: zero mentions of an undeclared name is
        # an honest 0, not a failure (CONTRIBUTING's two empties).
        code, out, _ = self.run_cli("callers", "-c", "base", "bogus")
        self.assertEqual(code, 0)
        self.assertEqual(out.split(), ["2", "0"])


class CallersTsvNamesEveryRow(SubjectLoop):
    """`callers -f tsv` [callers-tsv]: subject, caller, tag, theory, session,
    depth, locus -- every row attributed, several subjects one table."""

    def rows(self, out):
        return [ln.split("\t") for ln in out.splitlines()]

    def test_the_closure_with_depths(self):
        code, out, _ = self.run_cli("callers", "-r", "-f", "tsv", "base")
        self.assertEqual(code, 0)
        self.assertEqual(self.rows(out), [
            ["base", "mid", "LEMMA", "A", "S", "1", "A:3"],
            ["base", "other", "LEMMA", "A", "S", "1", "A:5"],
            ["base", "top", "LEMMA", "A", "S", "2", "A:4"],
        ])

    def test_located_hits(self):
        _, out, _ = self.run_cli("callers", "-f", "tsv", "base")
        self.assertEqual(self.rows(out), [
            ["base", "mid", "LEMMA", "A", "S", "1", "A:3"],
            ["base", "other", "LEMMA", "A", "S", "1", "A:5"],
        ])

    def test_several_subjects_are_one_table(self):
        _, out, _ = self.run_cli("callers", "-r", "-f", "tsv",
                                 "mid", "top", "base")
        self.assertNotIn("\n\n", out)
        self.assertEqual([r[0] for r in self.rows(out)],
                         ["mid", "base", "base", "base"])   # top: none

    def test_counts_are_labelled(self):
        _, out, _ = self.run_cli("callers", "-r", "-c", "-f", "tsv",
                                 "base", "top")
        self.assertEqual(self.rows(out), [["base", "3"], ["top", "0"]])


class CalleesTsvMirrorsCallers(SubjectLoop):
    """`callees -f tsv` [callees-tsv], issue #43: the same seven columns, so
    one parser reads both directions.  The locus is the callee's declaration.
    The fixture's lines: base 2, mid 3, top 4, other 5."""

    def rows(self, out):
        return [ln.split("\t") for ln in out.splitlines()]

    def test_direct(self):
        code, out, _ = self.run_cli("callees", "-f", "tsv", "top")
        self.assertEqual(code, 0)
        self.assertEqual(self.rows(out),
                         [["top", "mid", "LEMMA", "A", "S", "1", "A:3"]])

    def test_the_closure_with_depths(self):
        _, out, _ = self.run_cli("callees", "-r", "-f", "tsv", "top")
        self.assertEqual(self.rows(out), [
            ["top", "mid", "LEMMA", "A", "S", "1", "A:3"],
            ["top", "base", "LEMMA", "A", "S", "2", "A:2"],
        ])

    def test_several_subjects_are_one_table(self):
        _, out, _ = self.run_cli("callees", "-f", "tsv",
                                 "mid", "base", "other")
        self.assertEqual(self.rows(out), [
            ["mid", "base", "LEMMA", "A", "S", "1", "A:2"],
            ["other", "base", "LEMMA", "A", "S", "1", "A:2"],
        ])     # base: none

    def test_counts_are_labelled(self):
        _, out, _ = self.run_cli("callees", "-r", "-c", "-f", "tsv",
                                 "top", "base")
        self.assertEqual(self.rows(out), [["top", "2"], ["base", "0"]])

    def test_an_unknown_subject_still_fails_the_batch(self):
        code, out, err = self.run_cli("callees", "-f", "tsv", "top", "bogus")
        self.assertEqual((code, out), (1, ""))
        self.assertIn("'bogus'", err)


class TheTheoryVerbsTakeSeveral(SubjectLoop):
    """Issue #40: `outline`, and with it `theory` and `defs`, take a list of
    theories as `deps` and `uses` do, on the same spine."""

    def setUp(self):
        super().setUp()
        root = Path(self.root)
        (root / "B.thy").write_text(
            "theory B imports A begin\n"
            "definition d :: nat where \"d = 0\"\n"
            "lemma b: \"d = 0\" by (simp add: d_def)\nend\n")
        (root / "ROOT").write_text(
            "session S = HOL +\n  theories\n    A\n    B\n")

    def test_outline_gives_each_its_header(self):
        singles = [self.run_cli("outline", t)[1] for t in ("A", "B")]
        code, out, _ = self.run_cli("outline", "A", "B")
        self.assertEqual(code, 0)
        self.assertEqual(out, "\n".join(singles))
        self.assertEqual(out.count("Outline of "), 2)

    def test_theory_and_defs_counts_align(self):
        self.assertEqual(self.run_cli("theory", "-c", "A", "B")[1].split(),
                         ["4", "2"])
        self.assertEqual(self.run_cli("defs", "-c", "A", "B")[1].split(),
                         ["0", "1"])

    def test_an_unknown_theory_fails_the_batch(self):
        for verb in ("outline", "theory", "defs"):
            code, out, err = self.run_cli(verb, "A", "Bogus")
            self.assertEqual((code, out), (1, ""), verb)
            self.assertIn("'Bogus'", err)


if __name__ == "__main__":
    unittest.main()
