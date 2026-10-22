r"""A step is an Isar command, wherever the line breaks fall (#24) [step-command].

`_scan_steps` documented that it classifies "the Isar commands" of a proof,
but emitted one step per LINE: `have a: "P" using q by simp` was one step and
the same three commands on three lines were three.  `n_steps`, every per-step
mean, and M5c's `both` measured the layout as well as the proof — in one
corpus the step-count difference between two populations turned out to be
where they put `using` and `by`.

A line is now split at the proof commands it holds (found in the outer view,
outside parentheses), and a citation counts once, on the goal it serves.  The
invariant that pins it needs no hand-computed taxonomy: **put every command
on a line of its own, and the census record must not move**, except for the
fields that count lines.
"""

import os
import sys
import unittest
from collections import defaultdict

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402
import test_proof_owners  # noqa: E402

FIXTURES = os.path.join(os.path.dirname(__file__), "fixtures")

# #24's fixture: two lemmas, token for token identical.
FMT = r'''theory Fmt imports Main
begin

lemma one_line:
  fixes n :: nat
  shows "n + 0 = n \<and> 0 + n = n"
proof -
  have a: "n + 0 = n" using add_0_right by simp
  have b: "0 + n = n" unfolding add_0_left by simp
  show ?thesis using a b by blast
qed

lemma broken_lines:
  fixes n :: nat
  shows "n + 0 = n \<and> 0 + n = n"
proof -
  have a: "n + 0 = n"
    using add_0_right
    by simp
  have b: "0 + n = n"
    unfolding add_0_left
    by simp
  show ?thesis
    using a b
    by blast
qed

end
'''

# Shapes the fixture above does not reach: a calculation, a forward chain,
# an `apply` script, context commands sharing a line, a proof opened in
# mid-line, a dot proof, a method with a keyword-like argument.
MORE = r'''theory More imports Main
begin

lemma calc: "(a::nat) = a"
proof -
  have "a = a + 0" by simp also have "\<dots> = a" by simp
  finally show ?thesis .
qed

lemma chain:
  assumes h: "P" and k: "Q"
  shows "P \<and> Q"
proof -
  from h have p: "P" by assumption then have "P" by simp
  with k show ?thesis by (rule conjI [OF _ k])
qed

lemma script: "(x::nat) + 0 = x"
  apply (subst add_0_right) apply (rule refl) done

lemma ctx: "\<And>x::nat. x = x \<Longrightarrow> True"
proof - fix x :: nat assume e: "x = x" show True by (simp add: e) qed

lemma mid: "True \<and> True"
proof -
  have t: "True" proof - show "True" by simp qed
  show ?thesis using t by (cases rule: conjI) simp_all
qed

end
'''

# Fields that count lines rather than commands; everything else must hold.
LINE_FIELDS = {"proof_lines", "proof_lines_code", "entry_lines", "line"}


def reflow(sec) -> str:
    """The theory with every proof command that does not already start its
    line moved to a line of its own, indented under the line it left."""
    lines = sec.source()
    cuts: dict[int, set[int]] = defaultdict(set)
    for e in sec.entries:
        for c in shape.scan_commands(sec, e):
            if lines[c.line - 1][:c.col].strip():
                cuts[c.line].add(c.col)
    out: list[str] = []
    for i, ln in enumerate(lines, 1):
        cols = sorted(cuts.get(i, ()))
        if not cols:
            out.append(ln)
            continue
        indent = " " * (len(ln) - len(ln.lstrip()) + 2)
        out.append(ln[:cols[0]].rstrip())
        for a, b in zip(cols, cols[1:] + [len(ln)]):
            out.append(indent + ln[a:b].rstrip())
    return "\n".join(out) + "\n"


def records(sec) -> dict[str, dict]:
    """Census records by name — `TAG:name` for a proof owner, and a `#k`
    suffix on a repeat, since `?` names most owners and anonymous lemmas."""
    out = {}
    for pm in shape.analyze_sections([sec]):
        rec = shape.summary_record(shape.summarize(pm))
        key = (f"{pm.entry.tag}:{pm.entry.name}"
               if pm.entry in sec.proof_owners else pm.entry.name)
        k, base = 1, key
        while key in out:
            k += 1
            key = f"{base}#{k}"
        out[key] = {f: v for f, v in rec.items() if f not in LINE_FIELDS}
    return out


class TheIssueFixture(unittest.TestCase):

    def setUp(self):
        self.recs = records(section_from(FMT, "Fmt"))

    def test_the_two_layouts_agree(self):
        one, broken = self.recs["one_line"], self.recs["broken_lines"]
        self.assertEqual({**one, "lemma": ""}, {**broken, "lemma": ""})

    def test_the_count_is_commands(self):
        # have, using, by — three times — and qed.  `proof -` is structure.
        self.assertEqual(self.recs["one_line"]["n_steps"], 10)
        self.assertEqual(self.recs["one_line"]["n_goals"], 3)

    def test_both_is_per_goal(self):
        # `have a` and `have b` each introduce and cite (their `using` /
        # `unfolding`), whichever line that sits on; `show` cites a b.
        rec = self.recs["broken_lines"]
        self.assertEqual((rec["introduce"], rec["consume"], rec["both"]),
                         (2, 3, 2))

    def test_live_mean_is_per_command(self):
        # a: have a (0) .. using a b (7); b: have b (3) .. 7.
        # 1,1,1,2,2,2,2,2,0,0 over 10 commands.
        self.assertAlmostEqual(self.recs["one_line"]["live_mean"], 1.3)


class ReflowingMovesNothing(unittest.TestCase):

    def assert_invariant(self, text, theory):
        sec = section_from(text, theory)
        flowed_text = reflow(sec)
        self.assertNotEqual(flowed_text, text)    # the reflow did something
        before = records(sec)
        after = records(section_from(flowed_text, theory))
        self.assertEqual(set(before), set(after))
        for name in before:
            with self.subTest(name):
                self.assertEqual(before[name], after[name])

    def test_shape_fixture(self):
        with open(os.path.join(FIXTURES, "Shape.thy"), encoding="utf-8") as fh:
            self.assert_invariant(fh.read(), "Shape")

    def test_issue_fixture(self):
        self.assert_invariant(FMT, "Fmt")

    def test_more_shapes(self):
        self.assert_invariant(MORE, "More")

    def test_proof_owners(self):
        self.assert_invariant(test_proof_owners.THY, "Owners")


class WhatTheReflowFound(unittest.TestCase):
    """Two faults the AFP-wide reflow check turned up, each a place where the
    layout still reached a measurement."""

    def goals(self, body):
        thy = ('theory T imports Main begin\n'
               'lemma t: "True"\nproof -\n' + body +
               '  show ?thesis by simp\nqed\nend\n')
        sec = section_from(thy, "T")
        steps = shape._scan_steps(sec, sec.entries[0])
        shape.annotate_fanin(steps, sec)
        return [s for s in steps if s.kind == "goal"]

    def test_a_line_break_in_a_proposition_is_whitespace(self):
        # `\<and>` ending one line and `\<not>` opening the next are two
        # tokens; joining the lines with "" glued them into one
        # (Communication_C2KA:sink_nondet_stimcomm, after reflow).
        g = self.goals('  have "A \\<and>\n\\<not> B" sorry\n')[0]
        self.assertEqual(shape._stmt_tokens(g.stmt_text),
                         ["A", "\\<and>", "\\<not>", "B"])

    def test_a_subgoal_closes_itself_not_the_goal(self):
        # `subgoal by ...` closes the subgoal; the `have` it serves stays
        # open for the next one (ABY3_Protocols/Shuffle:252's shape).
        g = self.goals('  have p: "True"\n'
                       '    apply (rule a1)\n'
                       '    subgoal by (rule a2)\n'
                       '    subgoal by (rule a3)\n'
                       '    done\n')[0]
        self.assertEqual(g.fanin, 3)


class CommandsInMidLine(unittest.TestCase):
    """The split itself: what is a command, and what only looks like one."""

    def kws(self, name):
        sec = section_from(MORE, "More")
        e = next(e for e in sec.entries if e.name == name)
        return [c.kw for c in shape.scan_commands(sec, e)]

    def test_a_calculation_is_chain_plus_goal(self):
        self.assertEqual(self.kws("calc"),
                         ["proof", "have", "by", "also", "have", "by",
                          "finally", "show", ".", "qed"])

    def test_also_and_finally_are_plumbing(self):
        sec = section_from(MORE, "More")
        e = next(e for e in sec.entries if e.name == "calc")
        kinds = {s.kw: s.kind for s in shape._scan_steps(sec, e)}
        self.assertEqual((kinds["also"], kinds["finally"]),
                         ("plumbing", "plumbing"))

    def test_an_apply_script_on_one_line(self):
        self.assertEqual(self.kws("script"), ["apply", "apply", "done"])

    def test_a_keyword_inside_a_method_does_not_split(self):
        # `rule:` in `(cases rule: conjI)` and `_` / `OF` in brackets.
        self.assertEqual(self.kws("mid"),
                         ["proof", "have", "proof", "show", "by", "qed",
                          "show", "using", "by", "qed"])
        self.assertEqual(self.kws("chain")[-3:], ["show", "by", "qed"])

    def test_a_keyword_inside_a_term_or_comment_does_not_split(self):
        thy = ('theory T imports Main begin\n'
               'lemma t: "True"\n'
               'proof -\n'
               '  have "(\\<lambda>show. show) = id" (* then have *) by auto\n'
               '  show ?thesis \\<comment> \\<open>by simp\\<close> by simp\n'
               'qed\nend\n')
        sec = section_from(thy, "T")
        self.assertEqual([c.kw for c in shape.scan_commands(sec, sec.entries[0])],
                         ["proof", "have", "by", "show", "by", "qed"])

    def test_a_comment_lends_a_command_no_kind(self):
        # LSC:295, `proof(induction F) (* I should have ... *)`: the `have`
        # in the comment made the `proof` a goal step.  A command's kind is
        # its keyword's, and its text is read with comments blank.
        thy = ('theory T imports Main begin\n'
               'lemma t: "True"\n'
               '  proof (cases x) (* I should have "False" *)\n'
               '  show ?thesis by simp\n'
               'qed\nend\n')
        sec = section_from(thy, "T")
        steps = shape._scan_steps(sec, sec.entries[0])
        self.assertEqual([(s.kw, s.kind) for s in steps],
                         [("show", "goal"), ("by", "closing"),
                          ("qed", "closing")])

    def test_a_qualified_name_is_not_a_dot_proof(self):
        thy = ('theory T imports Main begin\n'
               'lemma t: "True"\n'
               'proof -\n'
               '  from 1.prems Foo.bar show ?thesis .\n'
               'qed\nend\n')
        sec = section_from(thy, "T")
        self.assertEqual([c.kw for c in shape.scan_commands(sec, sec.entries[0])],
                         ["proof", "from", "show", ".", "qed"])


if __name__ == "__main__":
    unittest.main()
