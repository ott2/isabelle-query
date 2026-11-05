r"""Every antiquotation kind that names a declaration is read [antiq-kinds].

Beyond `thm`, `const`, `term`, `typ` and `type`: the `_name` forms and
`const_syntax`, mostly written in ML, where an antiquotation is evaluated as
surely as in a document; `prop`, `term_type` and `value`, which hold a term;
`class` and `locale`; and ML's `\<^Const>` / `\<^Type>`, which name one
declaration and then take ML variables, so only their first name is read.

Hand-computed for the fixture (`Client` imports `Base`):

    cname   \<^const_name>           doc
    pname   @{prop "pname = 0"}       doc
    cfirst  \<^Const>‹cfirst targ›    doc
    targ    the same, second name     none: an ML variable there
    tname   @{type_name tname}        a `callers --antiquotations` row
    cls     @{class cls}              a row
    loc     @{locale loc}             a row
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

definition cname :: nat where "cname = 0"
definition pname :: nat where "pname = 0"
definition cfirst :: nat where "cfirst = 0"
definition targ :: nat where "targ = 0"
type_synonym tname = nat
class cls = fixes cop :: "'a \\<Rightarrow> 'a"
locale loc = fixes lx :: nat assumes "lx = lx"

end
"""

CLIENT = """\
theory Client
  imports Base
begin

ML \\<open>
  val a = \\<^const_name>\\<open>cname\\<close>
  fun b targ = \\<^Const>\\<open>cfirst targ\\<close>
\\<close>
text \\<open>@{prop "pname = 0"}, @{type_name tname}, @{class cls},
  @{locale loc}.\\<close>

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

    def test_the_new_kinds(self):
        rows = {ln.split()[1]: ln for ln in
                self.out(commands.cmd_unused).splitlines() if "lines)" in ln}
        doc = {n for n, r in rows.items() if r.endswith("[evidence: doc]")}
        self.assertEqual(doc, {"cname", "pname", "cfirst"})
        self.assertNotIn("evidence", rows["targ"])


class Callers(Fixture):

    def loci(self, name):
        return [r.split("\t")[-1] for r in self.out(
            commands.cmd_callers, name, fmt="tsv",
            antiquotations=True).splitlines()]

    def test_types_classes_and_locales(self):
        self.assertEqual(self.loci("tname"), ["Client:9"])
        self.assertEqual(self.loci("cls"), ["Client:9"])
        self.assertEqual(self.loci("loc"), ["Client:10"])

    def test_ml(self):
        self.assertEqual(self.loci("cname"), ["Client:6"])
        self.assertEqual(self.loci("cfirst"), ["Client:7"])
        self.assertEqual(self.loci("targ"), [])


if __name__ == "__main__":
    unittest.main()
