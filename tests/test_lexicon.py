r"""Where a name starts and ends, and which words are keywords (#42)
[api-names] [api-keywords].

The rule is Isabelle's `Lexicon.scan_longid`, which outer and inner syntax
share (`Pure/Isar/token.ML` calls it), with `Symbol.kind` deciding what a
letter is.  Every expected value below is read off that rule by hand.
"""

import tempfile
import unittest
from pathlib import Path

from isabelle_query import api


def names(text):
    return [n for _s, _e, n in api.scan_names(text)]


class TheIdentifierRule(unittest.TestCase):

    def test_where_a_name_ends(self):
        self.assertEqual(
            names("foo foo_bar foo' foo\\<^sub>1 \\<Gamma>foo M.foo foo.simps"),
            ["foo", "foo_bar", "foo'", "foo\\<^sub>1", "\\<Gamma>foo",
             "M.foo", "foo.simps"])

    def test_a_dot_with_no_name_after_it_is_not_part_of_one(self):
        self.assertEqual(names("using foo."), ["using", "foo"])
        self.assertEqual(names("foo..bar"), ["foo", "bar"])

    def test_variables_are_not_names(self):
        self.assertEqual(names("?x ?'b 'a x1"), ["x1"])

    def test_a_hol_string_is_not_a_name(self):
        self.assertEqual(names("''abc''"), [])

    def test_which_symbols_are_letters(self):
        # `\<lambda>` is not a letter (`symbol.ML`: "sic!"), nor are the
        # `\<var...>` forms; `\<AA>` and `\<x>` are.
        self.assertEqual(names("\\<lambda>x. f x"), ["x", "f", "x"])
        self.assertEqual(names("a\\<varepsilon>"), ["a"])
        self.assertEqual(names("\\<AA>b \\<x>"), ["\\<AA>b", "\\<x>"])

    def test_a_symbol_is_not_read_as_letters(self):
        self.assertEqual(names("\\<open>foo\\<close>"), ["foo"])
        self.assertEqual(names("A\\<and>B"), ["A", "B"])

    def test_a_subscript_needs_something_after_it(self):
        self.assertEqual(names("x\\<^sub>1"), ["x\\<^sub>1"])
        self.assertEqual(names("x\\<^sub>"), ["x"])

    def test_columns(self):
        self.assertEqual(list(api.scan_names("  M.foo")), [(2, 7, "M.foo")])

    def test_symbolic_identifiers_are_not_reported(self):
        self.assertEqual(names("using * ** foo"), ["using", "foo"])


THY = """\
theory T
  imports Main
begin

text \\<open>Prose about foo, and @{const foo}.\\<close>
definition foo :: nat where "foo = 0"
lemma bar: "foo = 0" (* foo in a comment, @{const foo} *)
  by (simp add: foo_def)
ML \\<open>val foo = @{term "foo + 1"}\\<close>

end
"""


class TheOccurrencesInATheory(unittest.TestCase):
    """Hand-read from THY: the theory name and `Main` are names; the prose
    on line 5 is not read but its antiquotation is; keywords outside a term
    are not names; the comment on line 7 is not read, antiquotation
    included; the ML `val foo` is ML's, and its antiquotation is read."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "T.thy").write_text(THY, encoding="utf-8")
        (d / "ROOT").write_text("session S = HOL +\n  theories T\n",
                                encoding="utf-8")
        self.sec = api.parse_root(d)[0]

    def tearDown(self):
        self._tmp.cleanup()

    def test_what_is_read(self):
        got = [(o.line, o.text, o.kind)
               for o in api.name_occurrences(self.sec)]
        self.assertEqual(got, [
            (1, "T", None), (2, "Main", None),
            (5, "foo", "const"),
            (6, "foo", None), (6, "nat", None), (6, "foo", None),
            (7, "bar", None), (7, "foo", None),
            (8, "simp", None), (8, "add", None), (8, "foo_def", None),
            (9, "foo", "term")])

    def test_columns_index_the_source(self):
        src = self.sec.source()
        for o in api.name_occurrences(self.sec):
            with self.subTest(o=o):
                self.assertEqual(src[o.line - 1][o.start:o.end], o.text)
                self.assertEqual(o.parts, tuple(o.text.split(".")))


class Keywords(unittest.TestCase):

    def test_under_main(self):
        for word, want in [("fun", True), ("datatype", True),
                           ("record", True), ("morphisms", True),
                           ("back", True), ("lemma", True),
                           ("domain", False), ("foo", False)]:
            with self.subTest(word=word):
                self.assertEqual(api.is_keyword(word), want)

    def test_a_project_s_imports_and_headers(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            (d / "A.thy").write_text(
                'theory A\n  imports HOLCF\n  keywords "my_cmd" :: thy_decl\n'
                'begin\nend\n', encoding="utf-8")
            (d / "ROOT").write_text("session S = HOLCF +\n  theories A\n",
                                    encoding="utf-8")
            secs = api.parse_root(d)
            kws = api.active_keywords(secs)
        self.assertIn("domain", kws)          # HOLCF's
        self.assertIn("fun", kws)             # HOL's, under HOLCF
        self.assertIn("my_cmd", kws)          # its own header's
        self.assertNotIn("foo", kws)


if __name__ == "__main__":
    unittest.main()
