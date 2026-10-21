r"""Why a goal step has no proposition, not just that it hasn't [bare-provenance].

`n_bare` pooled two unrelated things — *bare by construction* (`show ?thesis`,
`also`, `interpret`) and *the scanner found none* — and that pooling is what hid
issue #9(b) for as long as it did: a wrapped statement was booked as bare, where
nobody would look for a scanner fault.  So a rise in `n_bare` could not be read
as evidence about anything.

`bare_kinds` splits it three ways, and the buckets are named after the measured
population rather than guessed at — `scripts/probe_bare_provenance.py` over the
whole AFP, 195,733 bare goal steps out of 883,246:

    construction   173,613   88.70%   `?thesis`, `?case`, `also`, `interpret`
    unfound         11,766    6.01%   `obtain x where` with the statement below
    undelimited     10,354    5.29%   `hence False by simp` — written, unquoted

The third bucket is the one measuring found rather than confirmed: the
proposition IS on the line, written without quotes or a cartouche, which Isar
allows for a single term.  Nobody had counted those.

After #26 read a wrapped `obtain`, `unfound` is 498 (0.26%) of 188,289.
`unfound` is the residue and the point of the split — the only bucket whose
growth is evidence about the SCANNER rather than about writing style.

`n_bare` is unchanged and is the sum, so a stored census row stays comparable
with a new one.  `TheSumIsStillNBare` is the guard for that, and it is the one
that matters: a refinement that quietly redefines the field it refines would
invalidate every row already on disk.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402

# Every step below is a real AFP spelling, cited by the probe run above.
# Line numbers are load-bearing in the assertions; the theory is 40 lines.
BARE = r'''theory Bare
imports Main
begin

lemma by_construction: "True \<and> True"
proof -
  have a: "True" by simp
  also
  have "True" by simp
  interpret dummy_locale
  finally show ?thesis by simp
qed

lemma undelimited: "True"
proof -
  have nf: "\<not> False" by simp
  hence False by simp
  with \<open>\<not> False\<close> show False ..
  thus ?thesis by simp
qed

lemma unfound: "True"
proof -
  obtain x where
    "x = (0::nat)" by simp
  have
    "True" by simp
  thus ?thesis by simp
qed

lemma residue: "True"
proof -
  consider
    (a) "True" | (b) "\<not> True" by blast
  have False by(rule FalseE)
  show thesis.
  thus ?thesis by simp
qed

end
'''


def kinds(name):
    sec = section_from(BARE, "Bare")
    entry = next(e for e in sec.entries if e.name == name)
    pm = shape.analyze_proof(sec, entry)
    return pm, {s.line: s.bare for s in pm.goals}


class BareByConstruction(unittest.TestCase):
    r"""The step cannot carry an as-written proposition — 88.7% of the bare."""

    def setUp(self):
        self.pm, self.by_line = kinds("by_construction")

    def test_a_bare_also_is_not_a_goal_at_all(self):
        # `also` is a chain command (prf_decl, Pure.thy:81), not a goal, so it
        # has no bare kind because it is not a goal step [step-command].  It
        # used to be booked `construction` here when it stood on its own line,
        # and not at all when it led `also have` — the layout decided.
        self.assertNotIn(8, self.by_line)
        kinds = {s.line: s.kind for s in self.pm.steps if s.kw == "also"}
        self.assertEqual(kinds, {8: "plumbing"})

    def test_interpret_instantiates_rather_than_states(self):
        self.assertEqual(self.by_line[10], "construction")

    def test_show_thesis_is_construction(self):
        # `finally show ?thesis` — `_goal_command` takes the LAST goal keyword,
        # so this classifies as the `show` it is, not as the `finally`.  Both
        # routes land in `construction`; the test is that they agree.
        self.assertEqual(self.by_line[11], "construction")

    def test_a_stated_step_has_no_bare_kind(self):
        self.assertEqual(self.by_line[7], "")
        self.assertEqual(self.by_line[9], "")


class Undelimited(unittest.TestCase):
    r"""`hence False by simp` — the proposition is there, just not quoted."""

    def setUp(self):
        self.pm, self.by_line = kinds("undelimited")

    def test_a_bare_term_is_undelimited_not_unfound(self):
        # `hence False by simp` — E_Global_Invariants:727.
        self.assertEqual(self.by_line[17], "undelimited")

    def test_a_cited_cartouche_is_not_mistaken_for_the_statement(self):
        # `with \<open>\<not> False\<close> show False ..` —
        # E_Global_Invariants:1078.  The cited fact is written out in COMMAND
        # position, and `bare_kind` reads the command prefix, where
        # `_split_command_prefix` has blanked that span.  Classifying off the
        # raw line would find the cartouche and call this `unfound`.
        self.assertEqual(self.by_line[18], "undelimited")


class Unfound(unittest.TestCase):
    """The scanner looked and found nothing — the residue worth watching."""

    def setUp(self):
        self.pm, self.by_line = kinds("unfound")

    def test_obtain_with_the_statement_below_is_read(self):
        # `obtain x where` on its own line.  It was this bucket's largest
        # population (#26): 9,640 of the AFP's 12,026 `unfound`.  Read now,
        # so it is no longer bare at all.
        self.assertEqual(self.by_line[24], "")

    def test_a_wrapped_have_is_not_bare_at_all(self):
        # The half of issue #9(b) that IS fixed: `have` alone on its line with
        # a delimited statement below is read, so it never reaches `n_bare`.
        self.assertEqual(self.by_line[26], "")


class Residue(unittest.TestCase):
    """What `unfound` still holds after #26, and two spellings it no longer
    takes in by mistake."""

    def setUp(self):
        self.pm, self.by_line = kinds("residue")

    def test_case_named_consider_is_still_unfound(self):
        # `consider` / `(a) "P" | (b) "Q"`: the case names stand before the
        # delimiter, which `_statement_wrapped` does not read.  ~200 AFP rows.
        self.assertEqual(self.by_line[33], "unfound")

    def test_a_method_glued_to_its_by_is_undelimited(self):
        # `have False by(rule r)` — SDG, WellFormProgs.  No space before the
        # parenthesis, so splitting the rest at a blank put `by(rule` after
        # the term, which is not a proof word, and the step booked `unfound`.
        self.assertEqual(self.by_line[35], "undelimited")

    def test_a_dot_proof_glued_to_its_term_is_undelimited(self):
        # `show thesis.` — Binary_Code_Imprimitive:144.
        self.assertEqual(self.by_line[36], "undelimited")


class TheSumIsStillNBare(unittest.TestCase):
    """Guard: `bare_kinds` refines `n_bare`, it does not redefine it.

    Passes before and after in spirit — the invariant is what makes a census
    row written today comparable with one written last month.
    """

    def check(self, name):
        sec = section_from(BARE, "Bare")
        entry = next(e for e in sec.entries if e.name == name)
        ps = shape.summarize(shape.analyze_proof(sec, entry))
        self.assertEqual(sum(ps.bare_kinds.values()), ps.n_bare, name)
        return ps

    def test_every_proof_sums(self):
        for name in ("by_construction", "undelimited", "unfound"):
            with self.subTest(lemma=name):
                self.check(name)

    def test_every_bucket_key_is_present(self):
        ps = self.check("unfound")
        self.assertEqual(sorted(ps.bare_kinds), sorted(shape.BARE_KINDS))

    def test_a_stated_proof_has_an_all_zero_histogram(self):
        sec = section_from(
            'theory S\nimports Main\nbegin\n'
            'lemma allstated: "True"\nproof -\n  have "True" by simp\n'
            '  show "True" by simp\nqed\nend\n', "S")
        ps = shape.summarize(shape.analyze_proof(sec, sec.entries[0]))
        self.assertEqual(ps.n_bare, 0)
        self.assertEqual(set(ps.bare_kinds.values()), {0})


class NonGoalStepsCarryNoKind(unittest.TestCase):
    """`bare` is a property of a GOAL step; everything else stays ``""``."""

    def test_context_and_closing_steps(self):
        sec = section_from(BARE, "Bare")
        entry = next(e for e in sec.entries if e.name == "unfound")
        pm = shape.analyze_proof(sec, entry)
        other = [s for s in pm.steps if s.kind != "goal"]
        self.assertTrue(other)
        self.assertEqual({s.bare for s in other}, {""})


if __name__ == "__main__":
    unittest.main()
