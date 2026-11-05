r"""An antiquotation names a declaration in ONE name space [antiq-namespace].

Isabelle keeps facts, constants, types, classes and locales apart:
`definition foo` and `lemma foo` can coexist, and `@{const foo}` can only
mean the first.  The citation graph is keyed by bare name, so before this an
antiquotation counted for any entry spelled the same.

A fact antiquotation also names facts a constant or type declaration mints:
`@{thm gee_def}` is `definition gee`'s, `@{thm fib.simps}` is `fun fib`'s.
So its derived spellings are read back to the declaration, as the citation
graph reads them, and a theory-name prefix (`Base.foo`) names nothing.  (No
one-letter names here: the graph drops those, `--drop-names-upto`.)

Hand-computed for the fixture (`Client` imports `Base`), for `unused`:

    foo   LEMMA  @{thm Base.foo}         doc
    bar   DEF    @{const bar}            doc
    fib   FUN    @{thm fib.simps}        doc
    gee   DEF    @{thm gee_def}          doc
    baz   LEMMA  @{const baz}            none: no constant `baz`
    qux   DEF    @{thm qux}              none: no fact `qux`
    Maybe LEMMA  @{const Maybe}          none: that is the constructor

The last is the graph's node being a bare name: the constructor `Maybe` and
the lemma `Maybe` are one node, but a row is the lemma, and the constant
space holds only the constructor.  `callers --antiquotations Maybe` still
lists the site, since a subject typed there may be the constructor.
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

lemma foo: "True" by simp
definition bar :: nat where "bar = 0"
fun fib :: "nat \\<Rightarrow> nat" where "fib 0 = 0" | "fib (Suc n) = fib n"
definition gee :: nat where "gee = 0"
datatype col = Red | Blue
lemma baz: "True" by simp
definition qux :: nat where "qux = 0"
datatype tri = Yes | Maybe
lemma Maybe: "True" by simp

end
"""

CLIENT = """\
theory Client
  imports Base
begin

text \\<open>@{thm Base.foo}, @{const bar}, @{thm fib.simps}, @{thm gee_def},
  @{typ col}, @{const Red}, @{const baz}, @{thm qux}, @{const Maybe}.\\<close>

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

    def test_each_mention_counts_in_its_own_name_space(self):
        rows = {ln.split()[1]: ln for ln in
                self.out(commands.cmd_unused).splitlines() if "lines)" in ln}
        doc = {n for n, r in rows.items() if r.endswith("[evidence: doc]")}
        self.assertEqual(doc, {"foo", "bar", "fib", "gee"})
        self.assertNotIn("evidence", rows["baz"])
        self.assertNotIn("evidence", rows["qux"])
        self.assertNotIn("evidence", rows["Maybe"])


class Callers(Fixture):

    def rows(self, name):
        return self.out(commands.cmd_callers, name, fmt="tsv",
                        antiquotations=True).splitlines()

    def test_the_wrong_name_space_is_no_row(self):
        self.assertEqual(self.rows("baz"), [])
        self.assertEqual(self.rows("qux"), [])

    def test_a_constructor_and_a_type(self):
        self.assertEqual(len(self.rows("Red")), 1)
        self.assertEqual(len(self.rows("col")), 1)

    def test_a_constructor_sharing_a_lemma_s_name(self):
        self.assertEqual(len(self.rows("Maybe")), 1)

    def test_derived_spellings(self):
        self.assertEqual(len(self.rows("fib")), 1)
        self.assertEqual(len(self.rows("gee")), 1)


if __name__ == "__main__":
    unittest.main()
