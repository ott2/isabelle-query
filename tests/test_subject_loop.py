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


if __name__ == "__main__":
    unittest.main()
