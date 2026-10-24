r"""Goal steps the step scanner used to lose (issue #9).

Both faults came from one assumption in `shape._scan_steps`: that a proof line
is `command prefix` + *one* proposition, where the prefix ends at the line's
first `"` / `\<open>`.  Neither raised nor warned; each just produced a record
with a smaller number in it, which is the failure mode a metric tool has to be
most afraid of.

  (a) `from \<open>P\<close> have "Q"` — the cartouche is a *fact reference* in
      command position, so truncating there hid the `have` and the line booked
      as `plumbing`.  2.68% of AFP goal steps.
  (b) a proposition wrapped to the next line was discarded and the goal
      recorded as bare.  1.43% of goal steps, and 6.2% of everything reported
      in `n_bare`.

Each fixture below is written as the issue wrote it: the triggering shape, then
**the identical proof without it**.  Asserting fault == control is what makes
these regression tests rather than descriptions — it pins the property (the
spelling must not change the measurement), so it keeps holding if the numbers
themselves legitimately change.  (a)'s control spells the cited fact with
backquotes rather than dropping it: the cartouche is a citation (#31), so the
proof without it cites one fact fewer.

(a) is worth separating from the module docstring's general "line-anchored,
undercounts multi-*statement* lines" caveat, because the affected spelling is
specifically *modern* Isar: `from p have` and the backtick form were never
affected.  The undercount therefore grew as a development adopted current
style, so a measurement compared across releases saw a scanner artifact moving
in the same direction as the style trend.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import shape  # noqa: E402

SRC = r'''theory T imports Main
begin

lemma a_cartouche_citation: "True"
proof -
  have p: "True" by simp
  from p \<open>True\<close> have "True \<and> True" by simp
  show ?thesis by simp
qed

lemma a_control_backquoted: "True"
proof -
  have p: "True" by simp
  from p `True` have "True \<and> True" by simp
  show ?thesis by simp
qed

lemma b_wrapped_statement: "True"
proof -
  have
    "True \<and> True"
    by simp
  show ?thesis by simp
qed

lemma b_control_same_line: "True"
proof -
  have "True \<and> True" by simp
  show ?thesis by simp
qed

end
'''


def _steps(name):
    """The proof's steps, with `fanin` filled.

    `_scan_steps` leaves `fanin` at 0 — it is a later metric pass — so a test
    about citation *attribution* has to run `annotate_fanin` too, or it asserts
    0 == 0 and passes whatever the scanner did.
    """
    sec = section_from(SRC)
    entry = next(e for e in sec.entries if e.name == name)
    steps = shape._scan_steps(sec, entry)
    shape.annotate_fanin(steps, sec)
    return steps


def _goals(name):
    return [s for s in _steps(name) if s.kind == "goal"]


def _goal_shape(name):
    """A proof's goal steps as (goal_cmd, stmt, fanin), line numbers dropped so
    a fault case can be compared with its control.

    Goal steps only, deliberately.  The step model is line-anchored, so a proof
    that wraps its `by` onto its own line legitimately has one more `closing`
    step than the same proof written on one line — a difference in layout, not
    in shape, and not what these fixtures are about.
    """
    return [(s.goal_cmd, s.stmt_text, s.fanin) for s in _goals(name)]


class ACartoucheFactReferenceIsNotTheProposition(unittest.TestCase):

    def test_the_goal_behind_the_cartouche_is_emitted(self):
        # Was 2: the `from ... have` line classified as plumbing.
        self.assertEqual(len(_goals("a_cartouche_citation")), 3)

    def test_it_matches_the_same_proof_written_without_a_cartouche(self):
        self.assertEqual(_goal_shape("a_cartouche_citation"),
                         _goal_shape("a_control_backquoted"))

    def test_the_proposition_is_measured_not_the_cited_fact(self):
        # The trap in fixing (a): once the line is a goal step, a scanner that
        # still stops at the first delimiter extracts the *citation* `True` as
        # the statement.  The proposition is the delimiter after the keyword.
        goal = next(s for s in _goals("a_cartouche_citation")
                    if s.goal_cmd == "have" and s.line == 7)
        self.assertEqual(goal.stmt_text, r"True \<and> True")

    def test_the_citation_is_attributed_to_the_goal_that_makes_it(self):
        # Not merely an undercount: the lost goal's facts stayed pending and
        # attached to the NEXT goal, so `show ?thesis` was recorded as citing a
        # premise it does not cite.  A fault that MOVES a number is worse than
        # one that only subtracts.
        by_line = {s.line: s.fanin for s in _goals("a_cartouche_citation")}
        # `from p \<open>True\<close> have` cites p and the literal (#31)
        self.assertEqual(by_line[7], 2)
        self.assertEqual(by_line[8], 0)   # `show ?thesis` cites nothing

    def test_a_nested_cartouche_does_not_strand_its_closer(self):
        # Cartouches nest, so the skip needs the balanced scanner: a non-greedy
        # regex stops at the first `\<close>` and leaves the outer one in the
        # prefix — easy to miss, because it usually does not change the verdict.
        prefix, col = shape._split_command_prefix(
            r'from \<open>a \<open>b\<close> c\<close> have "Q" by simp')
        self.assertNotIn(r"\<close>", prefix)
        self.assertEqual(col, prefix.index('have') + len('have '))

    def test_a_line_with_no_goal_keyword_is_unchanged(self):
        # `using \<open>P\<close> by simp` states no proposition of its own; the
        # skip must not invent one.
        _prefix, col = shape._split_command_prefix(
            r'using \<open>P\<close> by simp')
        self.assertEqual(col, -1)

    def test_a_keyword_inside_a_cited_term_is_not_a_command(self):
        # Skipped spans are blanked, not deleted, so no token inside the cited
        # term can read as a command keyword.
        prefix, _col = shape._split_command_prefix(
            r'from \<open>have x\<close> by simp')
        self.assertNotIn("have", prefix)


class AWrappedStatementIsNotABareGoal(unittest.TestCase):

    def test_the_wrapped_proposition_is_found(self):
        goal = _goals("b_wrapped_statement")[0]
        self.assertEqual(goal.stmt_text, r"True \<and> True")

    def test_it_matches_the_same_proof_written_on_one_line(self):
        self.assertEqual(_goal_shape("b_wrapped_statement"),
                         _goal_shape("b_control_same_line"))

    def test_the_span_points_at_the_line_the_statement_is_on(self):
        goal = _goals("b_wrapped_statement")[0]
        self.assertEqual(goal.line, 20)          # the `have`
        self.assertEqual(goal.stmt_start, 21)    # the proposition

    def test_a_genuinely_bare_goal_stays_bare(self):
        # `show ?thesis` has a remainder after the keyword, so the lookahead
        # must not fire — this is the whole reason the rule is "the line ENDS
        # at the command", not "the line has no delimiter".
        bare = next(s for s in _goals("b_wrapped_statement")
                    if s.goal_cmd == "show")
        self.assertEqual((bare.stmt_start, bare.stmt_text), (0, ""))

    def test_a_labelled_wrapped_goal_is_found(self):
        sec = section_from('theory T imports Main\nbegin\n'
                           'lemma l: "True"\nproof -\n'
                           '  have key:\n    "True"\n    by simp\n'
                           '  show ?thesis by simp\nqed\nend\n')
        entry = next(e for e in sec.entries if e.name == "l")
        goal = [s for s in shape._scan_steps(sec, entry)
                if s.kind == "goal"][0]
        self.assertEqual((goal.label, goal.stmt_text), ("key", "True"))

    def test_a_command_followed_by_a_non_statement_stays_bare(self):
        # The lookahead requires the next live line to OPEN with a delimiter.
        sec = section_from('theory T imports Main\nbegin\n'
                           'lemma l: "True"\nproof -\n'
                           '  show ?thesis\n    by simp\nqed\nend\n')
        entry = next(e for e in sec.entries if e.name == "l")
        goal = [s for s in shape._scan_steps(sec, entry)
                if s.kind == "goal"][0]
        self.assertEqual(goal.stmt_text, "")


if __name__ == "__main__":
    unittest.main()
