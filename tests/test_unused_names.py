r"""`unused --names`: the rows without spans, for diffing [unused-names].

From #39: a before/after diff of `unused -r` around an edit was mostly
noise, because every entry below the edit moved its span and showed up as a
removed and an added row.  The `--names` rows carry the tag, the name, the
theory, the cascade depth and the evidence, and nothing that depends on
position.

Hand-computed for the fixture: `a_top` is cited by nobody, `b_mid` only by
`a_top`, `c_leaf` only by `b_mid`; `t_end` is a theorem nobody cites.
"""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

from isabelle_query import cli

THY = """\
theory T
  imports Main
begin
{pad}
lemma c_leaf: "True" by simp
lemma b_mid: "True" using c_leaf by simp
lemma a_top: "True" using b_mid by simp
theorem t_end: "True" by simp
{tail}
end
"""


class Names(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.d = Path(self._tmp.name)
        (self.d / "ROOT").write_text("session S = HOL +\n  theories T\n",
                                     encoding="utf-8")
        self.write("")

    def tearDown(self):
        self._tmp.cleanup()

    def write(self, pad, tail=""):
        (self.d / "T.thy").write_text(THY.format(pad=pad, tail=tail),
                                      encoding="utf-8")

    def run_cli(self, *args):
        out, err = io.StringIO(), io.StringIO()
        old = sys.argv
        sys.argv = ["query", "-R", str(self.d), *args]
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

    def test_rows(self):
        code, out, _ = self.run_cli("unused", "-r", "--names")
        self.assertEqual(code, 0)
        self.assertEqual([ln.split() for ln in out.splitlines()], [
            ["LEMMA", "c_leaf", "T", "[cascade", "depth", "2]"],
            ["LEMMA", "b_mid", "T", "[cascade", "depth", "1]"],
            ["LEMMA", "a_top", "T"],
            ["THEOREM", "t_end", "T", "[evidence:", "theorem]"]])

    def test_an_edit_above_changes_spans_not_rows(self):
        before_full = self.run_cli("unused", "-r")[1]
        before = self.run_cli("unused", "-r", "--names")[1]
        self.write('\nlemma pad: "True" by simp\n',
                   'lemma tail: "True" using a_top by simp\n')
        after_full = self.run_cli("unused", "-r")[1]
        after = self.run_cli("unused", "-r", "--names")[1]
        # Every span moved, but the only change is that `tail` now cites
        # `a_top`: the chain is one level deeper, `tail` its new root, and
        # `pad` a new uncited lemma.
        self.assertNotEqual(before_full, after_full)
        new = set(after.splitlines()) - set(before.splitlines())
        self.assertEqual(sorted(ln.split()[1] for ln in new),
                         ["a_top", "b_mid", "c_leaf", "pad", "tail"])

    def test_a_pure_move_is_no_diff(self):
        before = self.run_cli("unused", "-r", "--names")[1]
        self.write('\nlemma pad: "True" by simp\n')
        after = self.run_cli("unused", "-r", "--names")[1]
        self.assertEqual(set(after.splitlines()) - set(before.splitlines()),
                         {f"{'LEMMA':<11}  {'pad':<42}  T"})
        self.assertEqual(set(before.splitlines()) - set(after.splitlines()),
                         set())

    def test_usage_errors(self):
        for extra in (["--by-theory"], ["--roots"]):
            self.assertEqual(self.run_cli("unused", "--names", *extra)[0], 2)
        self.assertEqual(self.run_cli("unused", "facts", "--names")[0], 2)


if __name__ == "__main__":
    unittest.main()
