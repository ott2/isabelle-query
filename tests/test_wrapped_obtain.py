r"""A statement wrapped below its command is read, labels and all (#26).

0.7.0 read `have` alone on its line with the proposition opening the next.
The rest of #9's fault (b) was `obtain`: `obtain k where` ending the line,
or `obtain i j` with the `where` below, or the next line opening with a
label (`S0: "S 0 \<in> A"`).  Isar's grammar puts nothing else between the
command and the delimiter, so the look-ahead admits exactly that: an
optional `where` (required after variables that lack one) and an optional
label, then the delimiter.  Over the AFP, `unfound` fell from 12,026 to
~800 goal steps.

`interpret`, the issue's second row, is not taken up: it instantiates a
locale, and what follows it is a locale expression, not a proposition.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402

# The two lemmas of #26, differing only in where `obtain`'s line breaks.
ISSUE = r'''theory Wrap imports Main
begin

lemma wrapped:
  assumes "\<exists>k. k < (n::nat) \<and> P k"
  shows "\<exists>k. P k"
proof -
  obtain k where
    "k < n" and "P k"
    using assms by blast
  then show ?thesis by blast
qed

lemma flat:
  assumes "\<exists>k. k < (n::nat) \<and> P k"
  shows "\<exists>k. P k"
proof -
  obtain k where "k < n" and "P k" using assms by blast
  then show ?thesis by blast
qed

end
'''

# The forms the AFP writes, one goal per lemma; line 6 is the command.
FORMS = {
    # `then obtain i j` / `where lu: "..."` — Abstract-Rewriting/Seq:224.
    "vars_then_where": ('then obtain i j\n'
                        '    where lu: "i = (j::nat)" by auto',
                        'i = (j::nat)'),
    # `obtain S where` / `S0: "..." and` — Abstract_Rewriting:1996.
    "label_below": ('then obtain S where\n'
                    '    S0: "S = (0::nat)" and\n'
                    '    SN: "True"\n'
                    '    by auto',
                    'S = (0::nat)'),
    # `from Suc.prems obtain` / `valid: "..."` — HeapLift:1276: no variables,
    # so no `where`.
    "no_vars": ('from assms obtain\n'
                '    valid: "x = (0::nat)" by blast',
                'x = (0::nat)'),
    # `have` / `z1': "..."` — Counterclockwise_2D_Arbitrary:159.
    "have_label_below": ('have\n'
                         '    z1\': "x = (0::nat)" by simp',
                         'x = (0::nat)'),
    # `have [simp]:` / `"..."` — SASP_Checker:169.
    "attribute_label": ('have [simp]:\n'
                        '    "x = (0::nat)" by simp',
                        'x = (0::nat)'),
    # `have *:`, `have 1:`, `obtain \<Phi> where \<Phi>:`.
    "star_label": ('have *:\n    "x = (0::nat)" by simp', 'x = (0::nat)'),
    "numeric_label": ('have 1:\n    "x = (0::nat)" by simp', 'x = (0::nat)'),
    "symbol_label": ('obtain \\<Phi> where \\<Phi>:\n'
                     '    "\\<Phi> = (0::nat)" by simp',
                     '\\<Phi> = (0::nat)'),
}

# Forms that must stay bare: reading them would invent a statement.
DECLINED = {
    # Variables, no `where`, and the next line does not supply one.
    "vars_no_where": 'obtain i j\n    "i = (j::nat)" by auto',
    # `where` where the grammar has none.
    "have_where": 'have\n    where "x = (0::nat)" by simp',
    # A next line that is not a statement at all.
    "using_below": 'obtain k where\n    using assms by blast',
}


def lemma_with(body):
    return ('theory F imports Main\nbegin\n\n'
            'lemma t: assumes "x = (0::nat)" shows "True"\nproof -\n'
            f'  {body}\n  show ?thesis by simp\nqed\n\nend\n')


def first_goal(body):
    sec = section_from(lemma_with(body), "F")
    pm = shape.analyze_proof(sec, sec.entries[0])
    return pm.goals[0]


class TheIssueFixture(unittest.TestCase):

    def setUp(self):
        sec = section_from(ISSUE, "Wrap")
        self.pm = {e.name: shape.analyze_proof(sec, e) for e in sec.entries}

    def test_neither_is_unfound(self):
        for name in ("wrapped", "flat"):
            with self.subTest(name):
                self.assertEqual(
                    shape.bare_kind_counts(self.pm[name].steps)["unfound"], 0)

    def test_both_read_the_same_first_proposition(self):
        texts = {n: [s.stmt_text for s in self.pm[n].goals]
                 for n in ("wrapped", "flat")}
        self.assertEqual(texts["wrapped"], texts["flat"])
        self.assertEqual(texts["flat"][0], "k < n")


class WrappedForms(unittest.TestCase):

    def test_each_form_is_read(self):
        for name, (body, text) in FORMS.items():
            with self.subTest(name):
                g = first_goal(body)
                self.assertEqual(g.line, 6)
                self.assertEqual(g.stmt_start, 7)
                self.assertEqual(g.stmt_text, text)
                self.assertEqual(g.bare, "")

    def test_declined_forms_stay_bare(self):
        for name, body in DECLINED.items():
            with self.subTest(name):
                g = first_goal(body)
                self.assertEqual(g.stmt_text, "")
                self.assertEqual(g.bare, "unfound")


if __name__ == "__main__":
    unittest.main()
