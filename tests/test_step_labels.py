r"""A goal's label and proposition, where Isar's grammar puts them
[obtain-label].

`Step.label` read `CMD NAME:` only, so it missed `obtain x where key:`, where
the label follows `where` (28,188 of 28,965 such AFP lines), `have key [simp]:`,
and a name that starts with a digit or a symbol.  An unread label makes the
fact unnamed, and an unnamed fact is never live (M5b).  Over the AFP the
labels read went from 123,366 to 186,288 goal steps.

Two leftovers of #26 sit in the same prefix: a quoted TYPE (`obtain x ::
"nat set" where`) was read as the proposition, and `consider` with its case
names on the next line (`(a) "P" | (b) "Q"`) was `unfound`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402


def first_goal(body):
    thy = ('theory T imports Main begin\n'
           'lemma t: assumes "x = (0::nat)" shows "True"\nproof -\n'
           f'  {body}\n  show ?thesis by simp\nqed\nend\n')
    sec = section_from(thy, "T")
    pm = shape.analyze_proof(sec, sec.entries[0])
    return pm.goals[0], pm


class Labels(unittest.TestCase):

    def test_each_form(self):
        cases = {
            'have foo [simp]: "x = x" by simp': "foo",
            'have 1: "x = x" by simp': "1",
            'have \\<Phi>: "x = x" by simp': "\\<Phi>",
            'obtain y where hy: "y = x" by simp': "hy",
            'obtain y :: nat where hy: "y = x" by simp': "hy",
            'obtain y :: "nat" where hy: "y = x" by simp': "hy",
            'obtain hy: "x = x" by simp': "hy",
            'obtain y where\n    hy: "y = x" by simp': "hy",
            'then obtain y\n    where hy: "y = x" by simp': "hy",
            'have\n    z1\': "x = x" by simp': "z1'",
        }
        for body, label in cases.items():
            with self.subTest(body):
                self.assertEqual(first_goal(body)[0].label, label)

    def test_a_type_is_no_label(self):
        self.assertEqual(first_goal('obtain y :: nat where "y = x" '
                                    'by simp')[0].label, "")

    def test_an_obtained_label_is_live(self):
        # `hy` is born at its `obtain` and cited by the `using` below, so it
        # is live across those commands; unread, nothing was ever live.
        _g, pm = first_goal('obtain y where hy: "y = x" by simp\n'
                            '  have "y = x" using hy by simp')
        self.assertEqual(pm.live_max, 1)


class TypesAreNotPropositions(unittest.TestCase):

    def test_a_quoted_type_is_skipped(self):
        g, _ = first_goal('obtain y :: "nat" where "y = x" by simp')
        self.assertEqual(g.stmt_text, "y = x")

    def test_a_quoted_type_spanning_lines_is_never_the_statement(self):
        # Unterminated on its line, the type cannot be skipped; it must not
        # be measured as the proposition either.  `unfound` says so.
        g, _ = first_goal('obtain f :: "nat \\<Rightarrow>\n'
                          '    nat" where "f = id" by simp')
        self.assertEqual((g.stmt_text, g.bare), ("", "unfound"))


class ConsiderCasesBelow(unittest.TestCase):

    def test_case_names_before_the_proposition(self):
        g, _ = first_goal('consider\n    (a) "x = 0" | (b) "x \\<noteq> 0" '
                          'by blast')
        self.assertEqual(g.stmt_text, "x = 0")

    def test_a_case_with_its_own_variables(self):
        g, _ = first_goal('consider\n    (a) y where "y = x" | (b) "x = 1" '
                          'by blast')
        self.assertEqual(g.stmt_text, "y = x")


if __name__ == "__main__":
    unittest.main()
