"""The synthetic `<toplevel>` caller [toplevel-label].

A citation outside every entry (`declare`, `instance`, an anonymous `lemmas`) is attributed
to a per-theory node `THEORY:<toplevel>`.  It used to be named by the BARE
theory name, so over a corpus two same-named theories (AFP has nineteen
`Examples`) shared one node: the closure counted them once, and nothing could
tell which theory or session a row came from.
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
from support import brute_force_call_graph, cli  # noqa: E402

from isabelle_query.api import parse_root  # noqa: E402

ROOT = """session S0 = HOL +
  theories
    Base

session S1 in alpha = S0 +
  theories
    A

session S2 in beta = S0 +
  theories
    A
"""

BASE = """theory Base imports Main begin
lemma base: "True" by simp
lemma mid: "True" using base by simp
end
"""

# Top-level citations of `base` on line 2 and `mid` on line 3, in both.
A = """theory A imports "S0.Base" begin
declare base [simp]
declare mid [simp]
end
"""


class TwoTheoriesNamedA(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        (root / "ROOT").write_text(ROOT)
        (root / "Base.thy").write_text(BASE)
        for d in ("alpha", "beta"):
            (root / d).mkdir()
            (root / d / "A.thy").write_text(A)
        self.root = str(root)
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

    def rows(self, out):
        return [ln.split("\t") for ln in out.splitlines()]


class OneNodePerTheory(TwoTheoriesNamedA):

    def test_each_theory_gets_its_own_node(self):
        graph = cli._build_call_graph(parse_root(Path(self.root)))
        self.assertEqual(graph.callers["base"],
                         {"mid", "alpha/A:<toplevel>", "beta/A:<toplevel>"})

    def test_the_closure_counts_both(self):
        code, out, _ = self.run_cli("callers", "-r", "-c", "base")
        self.assertEqual((code, out.strip()), (0, "3"))

    def test_the_oracle_agrees(self):
        sections = parse_root(Path(self.root))
        fast = cli._build_call_graph(sections)
        ref = brute_force_call_graph(sections)
        self.assertEqual(fast.callers, ref.callers)
        self.assertEqual(fast.callees, ref.callees)


class TsvRowsAreFilled(TwoTheoriesNamedA):
    """Issue #15: a `<toplevel>` row carries a tag, its theory, its session
    and a locus, in both modes, and the two modes name it alike."""

    def test_closure_rows(self):
        code, out, _ = self.run_cli("callers", "-r", "-f", "tsv", "base")
        self.assertEqual(code, 0)
        self.assertEqual(self.rows(out), [
            ["base", "alpha/A:<toplevel>", "TOPLEVEL", "alpha/A", "S1", "1",
             "alpha/A:2"],
            ["base", "beta/A:<toplevel>", "TOPLEVEL", "beta/A", "S2", "1",
             "beta/A:2"],
            ["base", "mid", "LEMMA", "Base", "S0", "1", "Base:3"],
        ])

    def test_located_rows_name_the_caller_alike(self):
        _, out, _ = self.run_cli("callers", "-f", "tsv", "base")
        top = [r for r in self.rows(out) if r[2] == "TOPLEVEL"]
        self.assertEqual(top, [
            ["base", "alpha/A:<toplevel>", "TOPLEVEL", "alpha/A", "S1", "1",
             "alpha/A:2"],
            ["base", "beta/A:<toplevel>", "TOPLEVEL", "beta/A", "S2", "1",
             "beta/A:2"],
        ])

    def test_the_locus_is_the_edge_into_the_closure(self):
        # For `mid`, the node's first citation (line 2, of `base`) is not why
        # it is a caller; line 3 is.
        _, out, _ = self.run_cli("callers", "-r", "-f", "tsv", "mid")
        self.assertEqual([r[6] for r in self.rows(out)],
                         ["alpha/A:3", "beta/A:3"])

    def test_a_deeper_member_is_located_by_its_own_edge(self):
        # `base` <- `mid` <- alpha/A, which now cites only `mid`.
        (Path(self.root) / "alpha" / "A.thy").write_text(
            'theory A imports "S0.Base" begin\n'
            'declare mid [simp]\n'
            'end\n')
        _, out, _ = self.run_cli("callers", "-r", "-f", "tsv", "base")
        alpha = [r for r in self.rows(out) if r[3] == "alpha/A"]
        self.assertEqual(alpha, [["base", "alpha/A:<toplevel>", "TOPLEVEL",
                                  "alpha/A", "S1", "2", "alpha/A:2"]])


if __name__ == "__main__":
    unittest.main()
