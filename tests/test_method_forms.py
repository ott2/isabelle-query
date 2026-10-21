r"""How each method is applied, not only which (#25) [method-forms].

`method_kinds` buckets a discharged step by its leading method's name, so
`by (simp only:)` lands with `by simp` under `automation`, and
`apply (rule r)` with `by (rule r)` under `structural`.  In NDTHT the
populations differed 5.3x in `simp only:` and 7.3x in `apply` while their
`method_kinds` differed only by a structural share of 0.33 against 0.25.
`methods` keeps both distinctions, as `position:name/modifier` counts.
"""

import os
import sys
import unittest
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402

# #25's four lemmas.
ISSUE = r'''theory M imports Main
begin
lemma a: "x = y \<Longrightarrow> f x = f y" by (simp only:)
lemma b: "x = y \<Longrightarrow> f x = f y" by simp
lemma c: "x = y \<Longrightarrow> f x = f y" apply (rule arg_cong) apply assumption done
lemma d: "x = y \<Longrightarrow> f x = f y" by (rule arg_cong)
end
'''

# The other positions, modifiers, a combinator, and an argument whose `:`
# sits inside a quoted term (blank in the outer view, so no modifier).
MORE = r'''theory N imports Main
begin
lemma s: "rev (rev xs) = (xs::nat list)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by (auto simp add: foo intro: bar)
next
  case (Cons a xs)
  then show ?case
    apply (simp, auto)
    apply (rule_tac x="a:b" in exI)
    done
qed simp

lemma t: "True \<and> True"
proof
  show True ..
  show True .
qed

lemma u: "True"
proof -
  show ?thesis by (cases rule: foo) simp
qed
end
'''


def forms(text, theory):
    sec = section_from(text, theory)
    return {e.name: shape.analyze_proof(sec, e).methods for e in sec.entries}


class TheIssueFixture(unittest.TestCase):

    def test_modifier_and_position_are_kept(self):
        self.assertEqual(forms(ISSUE, "M"), {
            "a": {"by:simp/only": 1},
            "b": {"by:simp": 1},
            "c": {"apply:assumption": 1, "apply:rule": 1},
            "d": {"by:rule": 1},
        })


class Positions(unittest.TestCase):

    def setUp(self):
        self.f = forms(MORE, "N")

    def test_proof_and_qed_methods(self):
        s = self.f["s"]
        self.assertEqual(s["proof:induct/arbitrary"], 1)
        self.assertEqual(s["qed:simp"], 1)

    def test_the_first_modifier_of_the_leading_method(self):
        self.assertEqual(self.f["s"]["by:auto/add"], 1)

    def test_a_combinator_records_its_leading_method(self):
        self.assertEqual(self.f["s"]["apply:simp"], 1)

    def test_a_colon_in_a_quoted_argument_is_no_modifier(self):
        self.assertEqual(self.f["s"]["apply:rule_tac"], 1)

    def test_bare_proof_and_dot_proofs(self):
        self.assertEqual(self.f["t"], {"proof": 1, ".": 1, "..": 1})

    def test_proof_dash_and_a_terminal_second_method(self):
        # `by (cases rule: foo) simp`: the leading method is `cases`.
        self.assertEqual(self.f["u"], {"proof:-": 1, "by:cases/rule": 1})


class MethodKindsIsDerivable(unittest.TestCase):
    """`method_kinds` must be the `by` / `apply` forms bucketed by name, so a
    stored census row stays comparable with a new one."""

    def check(self, text, theory):
        sec = section_from(text, theory)
        for e in sec.entries:
            pm = shape.analyze_proof(sec, e)
            ps = shape.summarize(pm)
            derived = Counter({k: 0 for k in shape.METHOD_KIND_NAMES})
            for form, n in pm.methods.items():
                pos, _, rest = form.partition(":")
                if pos in ("by", "apply"):
                    derived[shape.method_kind(rest.split("/")[0])] += n
            with self.subTest(e.name):
                self.assertEqual(dict(derived), ps.method_kinds)

    def test_issue_fixture(self):
        self.check(ISSUE, "M")

    def test_more(self):
        self.check(MORE, "N")


if __name__ == "__main__":
    unittest.main()
