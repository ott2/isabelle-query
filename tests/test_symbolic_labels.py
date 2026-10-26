r"""A symbolic identifier names a fact (#35).

Isar's `name` admits a symbolic identifier, a run of `!#$%&*+-/<=>?@^_|~`,
so `have *: "P"` labels a fact `*` and `using *` cites it.  Every reader
took a name to start at a letter or digit, so a proof that labels with
`*`, `**`, `***` (about 12,500 labels in the Isabelle2025-2 AFP) read as
citing nothing and holding nothing.  A keyword spelled the same way is
not a name: the lexer prefers it, so `(rule r)+` and `simp?` stay
combinators.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import proof_locals, shape  # noqa: E402
from isabelle_query.graph import _cited_facts_on_line  # noqa: E402
from isabelle_query.premises import statement_of  # noqa: E402

# The issue's two fixtures.
SRC = r'''theory Sy imports Main
begin

lemma named:
  assumes a: "A" and b: "B"
  shows "A \<and> B"
proof -
  from a b show ?thesis by simp
qed

lemma symbolic:
  assumes *: "A" and **: "B"
  shows "A \<and> B"
proof -
  from * ** show ?thesis by simp
qed

lemma symbolic_using:
  assumes *: "A" and **: "B"
  shows "A \<and> B"
proof -
  show ?thesis using * ** by simp
qed

lemma symbolic_method:
  assumes *: "A" and **: "B"
  shows "A \<and> B"
proof -
  show ?thesis by (simp add: * **)
qed

lemma symbolic_OF:
  assumes *: "A" and **: "B" and r: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  shows "A \<and> B"
proof -
  show ?thesis by (rule r[OF * **])
qed

lemma named_OF:
  assumes a: "A" and b: "B" and r: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  shows "A \<and> B"
proof -
  show ?thesis by (rule r[OF a b])
qed

lemma named_live:
  shows "A \<longrightarrow> B \<longrightarrow> A \<and> B"
proof (intro impI)
  assume a: "A"
  assume b: "B"
  have c: "A \<and> B" using a b by simp
  show "A \<and> B" using a b c by simp
qed

lemma symbolic_live:
  shows "A \<longrightarrow> B \<longrightarrow> A \<and> B"
proof (intro impI)
  assume *: "A"
  assume **: "B"
  have ***: "A \<and> B" using * ** by simp
  show "A \<and> B" using * ** *** by simp
qed

lemma quoted:
  assumes *: "A" and **: "B" and 4: "C"
  shows "A \<and> B"
proof -
  have $: "A \<and> B" using "*" by (metis "**"(4))
  show ?thesis by (metis "$")
qed

lemma method_text:
  assumes "A" "B"
  shows "A \<and> B"
proof -
  have *: "A" using assms by simp
  have **: "B" using assms by simp
  show ?thesis by (use assms in \<open>simp add: * "**"\<close>)
qed

lemma glued:
  assumes "A" "B"
  shows "A"
proof -
  note * = assms(1)
  have **: "A" by (auto dest:*)
  show "A" apply (erule **; simp) done
qed

lemma unread_symbolic:
  assumes *: "A" and **: "B"
  shows "A"
proof -
  have $: "A" using * by simp
  show "A" using * by simp
qed

end
'''


def _steps(name):
    sec = section_from(SRC, theory="Sy")
    entry = next(e for e in sec.entries if e.name == name)
    steps = shape._scan_steps(sec, entry)
    shape.annotate_fanin(steps, sec)
    return sec, entry, steps


def _fanin(name):
    return [s.fanin for s in _steps(name)[2] if s.kind == "goal"]


def _live(name):
    sec, _, steps = _steps(name)
    return shape.live_fact_space(steps, sec)


def _cited(line):
    return _cited_facts_on_line(line)[0]


class FanIn(unittest.TestCase):

    def test_the_issue_case(self):
        for name in ("named", "symbolic", "symbolic_using",
                     "symbolic_method"):
            with self.subTest(name):
                self.assertEqual(_fanin(name), [2])
        self.assertEqual(_fanin("symbolic_OF"), _fanin("named_OF"))
        self.assertEqual(_fanin("symbolic_OF"), [3])

    def test_every_fact_position(self):
        for line, want in (("from * ** show ?thesis", {"*", "**"}),
                           ("with *** have x", {"***"}),
                           ("unfolding $ by simp", {"$"}),
                           ("by (metis * #)", {"*", "#"}),
                           ("using *[OF a] ++ by blast", {"*", "a", "++"}),
                           ("by (auto simp: ** foo)", {"**", "foo"})):
            with self.subTest(line):
                self.assertEqual(_cited(line), want)


class AQuotedName(unittest.TestCase):
    """Sledgehammer quotes a name that is not an identifier, and over the
    AFP a symbolic label is cited quoted about as often as not."""

    def test_is_the_same_fact(self):
        self.assertEqual(_cited('using "*" * by simp'), {"*"})
        self.assertEqual(_cited('by (metis "*" "**"(4) foo)'),
                         {"*", "**", "foo"})
        self.assertEqual(_cited('from "$"(2) "****"(1) have x'),
                         {"$", "****"})
        # `have $:` cites `*` by `using` and `**` by its closing method.
        self.assertEqual(_fanin("quoted"), [2, 1])

    def test_a_quoted_term_is_not(self):
        for line in ('by (subgoal_tac "P")', 'by (cases "x")',
                     'have "P" by simp', 'using "a b" by simp',
                     'by (metis "+")'):
            with self.subTest(line):
                self.assertEqual(_cited_facts_on_line(line), (set(), True))
        # An unknown method's quoted argument may be a term: no coverage
        # lost, as for a literal.
        self.assertEqual(_cited_facts_on_line('by (foo "*")'), (set(), True))


class LiveFactSpace(unittest.TestCase):

    def test_the_issue_case(self):
        self.assertEqual(_live("symbolic_live"), _live("named_live"))
        self.assertEqual(_live("symbolic_live"), (3, 2.0))

    def test_the_label_is_the_steps_own(self):
        _, _, steps = _steps("symbolic_live")
        self.assertIn("***", [s.label for s in steps])


class AKeywordIsNoName(unittest.TestCase):

    def test_combinators_and_syntax(self):
        # Read as names, `+` and `?` would start a method of their own and
        # cost coverage; `=` would be cited by `note`.
        for line, want in (("by (rule x)+", {"x"}),
                           ("apply (simp add: f)?", {"f"}),
                           ("by (simp | rule r)", {"r"}),
                           ("note x = a b", set())):
            with self.subTest(line):
                self.assertEqual(_cited_facts_on_line(line), (want, True))

    def test_a_marker_colon_and_a_semicolon_delimit(self):
        self.assertEqual(_cited("by (auto dest:* r)"), {"*", "r"})
        self.assertEqual(_cited("apply (erule *; simp)"), {"*"})
        self.assertEqual(_cited("by auto (metis assms(2 - 7) r)"),
                         {"assms", "r"})

    def test_a_glued_run_is_no_token(self):
        # `intro!:` is a marker, and `(2-)` a selection.
        self.assertEqual(_cited("by (force intro!: a)"), {"a"})
        self.assertEqual(_cited("using assms(2-) b by simp"), {"assms", "b"})


class TheOtherReaders(unittest.TestCase):

    def test_premises_carry_their_label(self):
        sec = section_from(SRC, theory="Sy")
        entry = next(e for e in sec.entries if e.name == "symbolic")
        self.assertEqual([p.label for p in statement_of(sec, entry).premises],
                         ["*", "**"])

    def test_unused_facts_reads_and_binds_them(self):
        sec = section_from(SRC, theory="Sy")
        rows = {(b.entry, b.name)
                for _, b in proof_locals.unread_locals([sec])}
        self.assertEqual(sorted(n for e, n in rows if e == "unread_symbolic"),
                         ["$", "**"])
        for entry in ("symbolic", "symbolic_using", "symbolic_method",
                      "symbolic_OF"):
            with self.subTest(entry):
                self.assertFalse([n for e, n in rows if e == entry])
        # Quoted uses read, and `"**"(4)` selects: it reads no fact `4`.
        self.assertEqual([n for e, n in rows if e == "quoted"], ["4"])
        # So in a cartouche of method text.
        self.assertEqual([n for e, n in rows if e == "method_text"], [])
        # Glued to a marker's colon, or before a `;`.
        self.assertEqual([n for e, n in rows if e == "glued"], [])


if __name__ == "__main__":
    unittest.main()
