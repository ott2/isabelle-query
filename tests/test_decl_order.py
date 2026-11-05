r"""A site above its own file's declaration does not name it [decl-order].

Isabelle reads a theory top to bottom.  A citation or antiquotation at
line 5 of `T` cannot mean the `late` that `T` declares at line 8: it names
an imported `late`, or none, and then the theory fails to check.  Deciding
visibility per theory made a theory see its own declarations wherever they
sat, so such a site was linked to the declaration below it.

Hand-computed for the fixture (`T` imports `Lib`; line numbers are `T`'s):

* `early` (5) cites `late` and `late2`, both declared below and nowhere
  else.  Neither edge exists: `late` is cited only by `after` (12), and
  `late2` by nothing, so it is unused.
* `early2` (6) cites `shared`, which `T` declares below (10) and `Lib`
  declares too.  The edge stays: it goes to `Lib`'s, and the graph's node
  is the name.
* The `@{const later_c}` at 7 sits above `later_c` (11), so it is not
  `doc` evidence for it.
"""

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli, commands  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402

LIB = """\
theory Lib
  imports Main
begin
lemma shared: "True" by simp
end
"""

T = """\
theory T
  imports Lib
begin

lemma early: "True" using late late2 by simp
lemma early2: "True" using shared by simp
text \\<open>@{const later_c}\\<close>
lemma late: "True" by simp
lemma late2: "True" by simp
lemma shared: "True" by simp
definition later_c :: nat where "later_c = 0"
lemma after: "True" using late by simp
end
"""


class Fixture(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "Lib.thy").write_text(LIB, encoding="utf-8")
        (d / "T.thy").write_text(T, encoding="utf-8")
        (d / "ROOT").write_text("session S = HOL +\n  theories T\n",
                                encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def out(self, fn, *args, **kw):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            fn(self.sections, *args, CmdFlags(**kw))
        return buf.getvalue()


class CitationsAboveTheDeclaration(Fixture):

    def test_callers_skips_the_site_above(self):
        self.assertEqual(self.out(commands.cmd_callers, "late", fmt="tsv"),
                         "late\tafter\tLEMMA\tT\tS\t1\tT:12\n")

    def test_the_graph_has_no_edge_from_above(self):
        self.assertEqual(
            self.out(commands.cmd_callers, "late", fmt="tsv", recursive=True),
            "late\tafter\tLEMMA\tT\tS\t1\tT:12\n")
        self.assertEqual(self.out(commands.cmd_callees, "early",
                                  fmt="tsv"), "")

    def test_an_imported_declaration_keeps_the_edge(self):
        self.assertEqual(
            self.out(commands.cmd_callers, "shared", fmt="tsv").splitlines(),
            ["shared\tearly2\tLEMMA\tT\tS\t1\tT:6"])

    def test_unused(self):
        rows = {ln.split()[1]: ln for ln in
                self.out(commands.cmd_unused).splitlines() if "lines)" in ln}
        self.assertEqual(sorted(rows),
                         ["after", "early", "early2", "late2", "later_c"])
        self.assertNotIn("evidence", rows["later_c"])


if __name__ == "__main__":
    unittest.main()
