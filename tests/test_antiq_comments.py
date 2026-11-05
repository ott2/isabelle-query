r"""An antiquotation Isabelle never checks is no reference [antiq-comment].

`(* ... *)` is a comment that Isabelle discards, and `\<^cancel>` text is
discarded too, so an antiquotation inside either is neither verified nor
broken by deleting what it names.  A `\<comment>` note is document text, and
an ML body is evaluated: antiquotations in both are checked.

Hand-computed for the fixture (`Client` imports `Base`):

    cone    (* ... *), across two lines     none
    ctwo    \<^cancel>                       none
    cthree  ML body                          doc
    cfour   \<comment> note                  doc
    cfive   (* ... *), then live text on     doc   (the later mention)
            the next line
    csix    ML body, below a line that       doc
            starts with an ML comment

The last is why the tokenizer decides this: from the spans alone, a line
ending in an ML comment's `*)` and the next starting with `(*` look exactly
like one comment region closing and another opening.
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

BASE = """\
theory Base
  imports Main
begin

definition cone :: nat where "cone = 0"
definition ctwo :: nat where "ctwo = 0"
definition cthree :: nat where "cthree = 0"
definition cfour :: nat where "cfour = 0"
definition cfive :: nat where "cfive = 0"
definition csix :: nat where "csix = 0"

end
"""

CLIENT = """\
theory Client
  imports Base
begin

(* An aside that names
   @{const cone} and @{const cfive}. *)
text \\<open>Only @{const cfive} here.\\<close>
\\<^cancel>\\<open>@{const ctwo}\\<close>
ML \\<open>
  val t = @{term "cthree"} (* an ML comment to the end of the line *)
(* an ML comment at the start of a line, then live ML: *)
  val u = @{term "csix"}
\\<close>
lemma l: "True" \\<comment> \\<open>see @{const cfour}\\<close>
  by simp

end
"""


class Fixture(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "Base.thy").write_text(BASE, encoding="utf-8")
        (d / "Client.thy").write_text(CLIENT, encoding="utf-8")
        (d / "ROOT").write_text("session S = HOL +\n  theories Client\n",
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


class Evidence(Fixture):

    def test_only_checked_antiquotations_count(self):
        rows = {ln.split()[1]: ln for ln in
                self.out(commands.cmd_unused).splitlines() if "lines)" in ln}
        doc = {n for n, r in rows.items() if r.endswith("[evidence: doc]")}
        self.assertEqual(doc, {"cthree", "cfour", "cfive", "csix"})


class Callers(Fixture):

    def loci(self, name):
        return [r.split("\t")[-1] for r in self.out(
            commands.cmd_callers, name, fmt="tsv",
            antiquotations=True).splitlines()]

    def test_a_comment_is_no_row(self):
        self.assertEqual(self.loci("cone"), [])
        self.assertEqual(self.loci("ctwo"), [])

    def test_the_checked_ones_are(self):
        self.assertEqual(self.loci("cthree"), ["Client:10"])
        self.assertEqual(self.loci("cfour"), ["Client:14"])
        self.assertEqual(self.loci("csix"), ["Client:12"])
        self.assertEqual(self.loci("cfive"), ["Client:7"])


if __name__ == "__main__":
    unittest.main()
