r"""`show --premises`: one line per premise, keyed by how a proof cites it
[show-premises].

Issue #17: an abstract-versus-theorem audit wants the premises alone, and
`show` had no view short by construction.  Each premise is keyed by the name
Isabelle gives it -- `assms(k)` for `assumes`, `that(k)` for `if`, numbered
across every element -- plus its own label; a premise written inside the term
(`"P \<Longrightarrow> C"`) has no name and is keyed by position.  Expected
values are read off the Isar grammar, not off the implementation.
"""

import contextlib
import io
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import cli, commands  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402
from isabelle_query.premises import read_statement, split_imp  # noqa: E402


def rows(text):
    st = read_statement(text)
    return [(p.kind, p.cite, p.label, p.text) for p in st.premises], \
        st.conclusions, st.cases


class LongForm(unittest.TestCase):

    def test_numbering_runs_across_elements_and_groups(self):
        got = rows(r'''lemma foo [simp]:
  fixes x :: "nat"
  assumes wf: "well_formed M" "P \<Longrightarrow> Q" and \<open>0 < q\<close>
  assumes k2: "2 \<le> k"
  defines "d \<equiv> x"
  shows c: "A" and "B (x::nat)"
  by simp''')
        self.assertEqual(got, ([
            ("assumes", "assms(1)", "wf(1)", "well_formed M"),
            ("assumes", "assms(2)", "wf(2)", "P \\<Longrightarrow> Q"),
            ("assumes", "assms(3)", "", "0 < q"),
            ("assumes", "assms(4)", "k2", "2 \\<le> k"),
            ("defines", "", "", "d \\<equiv> x"),
        ], 2, 0))

    def test_bare_propositions(self):
        # Isar accepts a one-token proposition unquoted.
        self.assertEqual(rows("theorem T4:\n  assumes transitivity\n"
                              "  shows Quasitransit\n  by metis"),
                         ([("assumes", "assms(1)", "", "transitivity")], 1, 0))

    def test_keyword_against_a_cartouche(self):
        self.assertEqual(
            rows("lemma x: assumes h:\\<open>a\\<close> \\<open>b\\<close>\n"
                 "  shows\\<open>c\\<close> by simp"),
            ([("assumes", "assms(1)", "h(1)", "a"),
              ("assumes", "assms(2)", "h(2)", "b")], 1, 0))

    def test_obtains_counts_cases(self):
        self.assertEqual(
            rows('theorem t: assumes "A" obtains x where "P x" | y where '
                 '"Q y" using assms by blast'),
            ([("assumes", "assms(1)", "", "A")], 0, 2))


class ShortForm(unittest.TestCase):

    def test_if_premises_are_that(self):
        got, n, _ = rows(r'lemma bar: "C" if h: "P" and "Q" for x by simp')
        self.assertEqual((got, n), ([("if", "that(1)", "h", "P"),
                                     ("if", "that(2)", "", "Q")], 1))

    def test_no_premises(self):
        self.assertEqual(rows('lemma simple: "x = x" ..'), ([], 1, 0))

    def test_several_conclusions_are_not_split(self):
        # Each conclusion would have premises of its own.
        self.assertEqual(rows(r'lemma "A \<Longrightarrow> B" "C"'), ([], 2, 0))


class PremisesInsideTheTerm(unittest.TestCase):

    def test_outermost_implications_only(self):
        self.assertEqual(
            split_imp(r"A \<Longrightarrow> (B \<Longrightarrow> C) "
                      r"\<Longrightarrow> D"),
            ["A", "(B \\<Longrightarrow> C)", "D"])

    def test_bracket_list(self):
        self.assertEqual(split_imp(r"\<lbrakk>a; b \<le> c\<rbrakk> "
                                   r"\<Longrightarrow> R"),
                         ["a", "b \\<le> c", "R"])

    def test_an_outer_meta_quantifier_is_stripped(self):
        self.assertEqual(split_imp(r"\<And>x. P x \<Longrightarrow> Q x"),
                         ["P x", "Q x"])

    def test_a_later_quantifier_scopes_the_rest(self):
        self.assertEqual(
            split_imp(r"A \<Longrightarrow> \<And>x. B x \<Longrightarrow> C"),
            ["A", "\\<And>x. B x \\<Longrightarrow> C"])

    def test_rel_fun_is_not_an_implication(self):
        self.assertEqual(split_imp("(R ===> S) f g ==> T"),
                         ["(R ===> S) f g", "T"])

    def test_keyed_after_the_named_premises(self):
        got, _, _ = rows(r'''lemma m: assumes "P" shows "Q \<Longrightarrow> R"''')
        self.assertEqual(got, [("assumes", "assms(1)", "", "P"),
                               ("term", "", "", "Q")])


THY = r'''theory T imports Main begin
lemma lin:
  assumes wf: "well_formed M"
    and "0 < q"
  shows "A" and "B" and "C"
  by simp
lemma arrow: "P \<Longrightarrow> Q" by simp
definition d :: nat where "d = 0"
end
'''


class TheView(unittest.TestCase):

    def show(self, name):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            commands.cmd_show([section_from(THY, "T")], name,
                              CmdFlags(premises=True))
        return out.getvalue().splitlines()

    def test_aligned_and_counted(self):
        self.assertEqual(self.show("lin")[1:], [
            "  assms(1) wf:  well_formed M",
            "  assms(2):     0 < q",
            "  shows: 3 conclusions"])

    def test_term_premises(self):
        self.assertEqual(self.show("arrow")[1:], [
            "  term 1:  P", "  shows: 1 conclusion"])

    def test_not_a_goal(self):
        self.assertEqual(self.show("d")[1:], ["  (no goal statement: a DEF)"])

    def test_the_header_is_the_usual_one(self):
        self.assertTrue(self.show("lin")[0].startswith("--- lin (LEMMA) — T.thy"))


class TheFlag(unittest.TestCase):

    def test_excludes_the_other_slices(self):
        for other in ("--statement", "-V"):
            with self.subTest(other=other):
                err = io.StringIO()
                with contextlib.redirect_stderr(err), \
                        self.assertRaises(SystemExit):
                    cli._build_parser().parse_args(
                        ["show", "--premises", other, "x"])
                self.assertIn("not allowed with", err.getvalue())


if __name__ == "__main__":
    unittest.main()
