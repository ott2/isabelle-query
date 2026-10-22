r"""`unused --locals`: proof-local names bound and never read (issue #12).

The fixture's answer is hand-read, one lemma per rule the scan has to get
right.  Nine bindings are unread:

* `flat` — `c` is mentioned only in a comment; `d` is a `note` nobody cites.
  `a` (cited by `note d = a`) and `b` are read; `e` is consumed by `then`.
* `shadow` — the inner `f` (line 22) is out of scope at line 25, which reads
  the outer one; the first `f` is read by the second's own `using f`, because
  a label binds only when its proof is done.
* `branches` — the `h` after `next` (line 35); the `True` branch's `h` is read
  in its own branch, which a flat occurrence count would take for both.
* `binders` — `obtain … k:` (41), `define m` (43), `let ?p` (46), and `t`
  (50), whose `[rule_format]` transforms the fact without declaring it
  anywhere.  `k2`, `n` (through `n_def`), `?q`, and `s [simp]` are used.
* `calc` — `p`, bound inside `{ }`; `q` and `r` feed `moreover`/`ultimately`.
"""

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from support import cli  # noqa: E402
from isabelle_query import proof_locals  # noqa: E402

LOCALS_FIX = r'''theory Locals_Fix
  imports Main
begin

lemma flat: "True"
proof -
  have a: "True" by simp
  have b: "True" by simp
  have c: "True" using b by simp
  note d = a
  have e: "True" by simp
  then have "True" by simp
  show ?thesis by simp (* using c *)
qed

lemma shadow: "True"
proof -
  have f: "True" by simp
  have f: "True" using f by simp
  have g: "True"
  proof -
    have f: "True" by simp
    show ?thesis by simp
  qed
  show ?thesis using f g by simp
qed

lemma branches: "x \<or> \<not> x"
proof (cases x)
  case True
  have h: "x" using True by simp
  show ?thesis using h by simp
next
  case False
  have h: "\<not> x" using False by simp
  show ?thesis using False by simp
qed

lemma binders: "True"
proof -
  obtain y :: nat where k: "y = y" and k2: "y = 0" by simp
  have "y = 0" using k2 .
  define m where "m = (0::nat)"
  define n where "n = (1::nat)"
  have "n = 1" unfolding n_def by simp
  let ?p = "True"
  let ?q = "True"
  have ?q by simp
  have s [simp]: "True" by simp
  have t [rule_format]: "True" by simp
  show ?thesis by simp
qed

lemma calc: "True"
proof -
  {
    have p: "True" by simp
  }
  have q: "True" by simp
  moreover have r: "True" by simp
  ultimately show ?thesis by simp
qed

end
'''

EXPECTED = [
    (9, "c", "have", "flat"),
    (10, "d", "note", "flat"),
    (22, "f", "have", "shadow"),
    (35, "h", "have", "branches"),
    (41, "k", "obtain", "binders"),
    (43, "m", "define", "binders"),
    (46, "?p", "let", "binders"),
    (50, "t", "have", "binders"),
    (57, "p", "have", "calc"),
]


class _Root(unittest.TestCase):
    """A one-theory root; subclasses set THEORIES = {name: text}."""
    THEORIES = {"Locals_Fix": LOCALS_FIX}

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        for name, text in self.THEORIES.items():
            (self.dir / f"{name}.thy").write_text(text, encoding="utf-8")
        (self.dir / "ROOT").write_text(
            "session Fix = HOL +\n  theories\n"
            + "".join(f"    {n}\n" for n in self.THEORIES), encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def unread(self, theory=None):
        secs = [s for s in self.sections
                if theory is None or s.theory == theory]
        return [(b.line, b.name, b.kind, b.entry)
                for _, b in proof_locals.unread_locals(secs)]

    def run_cli(self, *argv):
        """(stdout, exit status) of `unused ARGV`."""
        ns = cli._build_parser().parse_args(["unused", *argv])
        out, code = io.StringIO(), 0
        with contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(io.StringIO()):
            try:
                ns.func(ns)
            except SystemExit as e:
                code = e.code
        return out.getvalue(), code


class HandReadFixture(_Root):

    def test_exactly_the_hand_read_rows(self):
        self.assertEqual(self.unread(), EXPECTED)

    def test_count(self):
        self.assertEqual(self.run_cli("--locals", "-c"), ("9\n", 0))

    def test_keep_names_deliberate_ones(self):
        out, _ = self.run_cli("--locals", "-c", "--keep", "c,d")
        self.assertEqual(out, "7\n")

    def test_rows_are_pasteable_loci(self):
        out, _ = self.run_cli("--locals")
        first = out.splitlines()[0].split()
        self.assertEqual(first, ["Locals_Fix:9", "c", "have", "flat"])


class Selection(_Root):
    """PATH selects PROOFS: a window or entry picks the proofs it touches."""

    def path(self):
        return str(self.dir / "Locals_Fix.thy")

    def test_entry_selector(self):
        out, code = self.run_cli("--locals", "-c", f"{self.path()}:shadow")
        self.assertEqual((out, code), ("1\n", 0))

    def test_window_selects_whole_proofs(self):
        # 30..31 lies inside `branches`; its unread `h` is on line 35.
        out, _ = self.run_cli("--locals", f"{self.path()}:30..31")
        self.assertIn("Locals_Fix:35", out)
        self.assertEqual(len(out.splitlines()), 1)

    def test_two_selectors_on_one_file_add_up(self):
        out, _ = self.run_cli("--locals", "-c", f"{self.path()}:shadow",
                              f"{self.path()}:calc")
        self.assertEqual(out, "2\n")

    def test_unknown_entry_is_unresolved(self):
        self.assertEqual(self.run_cli("--locals", f"{self.path()}:nosuch")[1],
                         1)

    def test_paths_need_locals(self):
        # Entry-level `unused` is corpus-wide by contract: no PATH scoping.
        self.assertEqual(self.run_cli(self.path())[1], 2)

    def test_locals_rejects_roots(self):
        # `-r` is the premise cascade (issue #20); a forest of proof-local
        # names means nothing.
        self.assertEqual(self.run_cli("--locals", "--roots")[1], 2)


# Each case below was a false report on the AFP before the rule it names.
CORNERS = r'''theory Corners
  imports Main
begin

lemma from_this: "True"
proof -
  have a: "True" by simp
  from this show ?thesis by simp
qed

lemma attr_args: "True"
proof -
  note defs = TrueI
  have b [unfolded defs]: "True" by simp
  show ?thesis using b by simp
qed

lemma qualified: "True"
proof -
  have c: "True" by simp
  show ?thesis using local.c by simp
qed

lemma define_for: "True"
proof -
  define f where "f i = (i::nat)" for i
  have "f 0 = 0" by (simp add: f_def)
  show ?thesis by simp
qed

lemma sup_markup: "True"
proof -
  let ?R = "\<lambda>x y. x = (y::nat)"
  have "?R\<^sup>*\<^sup>* 0 0" by simp
  show ?thesis by simp
qed

lemma text_inside: "True"
proof -
  have d: "True" by simp
  text \<open>A remark in the middle of a proof.\<close>
  show ?thesis using d by simp
qed

lemma dup_label: "True"
proof -
  obtain x :: nat where e: "x = x" and e: "x = 0" by simp
  show ?thesis using e by simp
qed

lemma greek_define: "True"
proof -
  define \<epsilon> where eps: "\<epsilon> = (0::nat)"
  have "\<epsilon> = 0" using eps by simp
  show ?thesis by simp
qed

end
'''


class Corners(_Root):
    THEORIES = {"Corners": CORNERS}

    def test_only_the_shadowed_duplicate(self):
        # Every lemma but the last reads its binding.  In the last, the second
        # `e` shadows the first, so the first cannot be reached by any reader.
        self.assertEqual(self.unread(), [(47, "e", "obtain", "dup_label")])


# Facts read by STATEMENT, not name (issue #27) [fact-method].  Hand-read:
# `by fact` (9) reads the premise `flag_alphabet`; `(fact | …)+` (17) reads
# `rd'`; `fact u` (25) reads `u` alone, so `v` stays unread; `‹(1::nat) = 1›`
# (33) reads `p`, whose statement is split over two lines, and not `q`.  A
# goal's labels bind after its method: line 39's `a` cites line 38's, and
# `own`'s `by fact` (45) cannot read `own` itself.
FACTS = r'''theory Facts
  imports Main
begin

lemma by_statement:
  assumes flag_alphabet: "x \<in> {0, 3::nat}"
  shows "x \<in> {0, 3::nat}"
proof -
  have flag_symbol: "x \<in> {0, 3::nat}" by fact
  show ?thesis using flag_symbol by simp
qed

lemma combinator: "True"
proof -
  have rd': "True" by simp
  have lap: "True"
    by (rule TrueI) (fact | rule refl)+
  show ?thesis using lap by simp
qed

lemma with_argument: "True"
proof -
  have u: "True" by simp
  have v: "True" by simp
  show ?thesis by (fact u)
qed

lemma literal: "True"
proof -
  have p: "(1::nat) =
    1" by simp
  have q: "(2::nat) = 2" by simp
  show ?thesis using \<open>(1::nat) = 1\<close> by simp
qed

lemma method_reads_the_old_label: "True"
proof -
  have a: "True" by simp
  have a: "True" by (simp add: a)
  show ?thesis using a by simp
qed

lemma own_fact_method: "True"
proof -
  have own: "True" by fact
  show ?thesis by simp
qed

end
'''


class ReadByStatement(_Root):
    THEORIES = {"Facts": FACTS}

    def test_exactly_the_hand_read_rows(self):
        self.assertEqual(self.unread(), [
            (24, "v", "have", "with_argument"),
            (32, "q", "have", "literal"),
            (45, "own", "have", "own_fact_method"),
        ])


# The lines that bind each name (issue #27) [local-spans].  Hand-read, every
# binding unread (an unlabelled `have` sits before each `moreover` / `then`
# so that neither reads a labelled fact):
#   a 7..8, its `by` on the next line;  b, c share line 9;  d, e are two
#   clauses of line 10;  f runs 11..14, from its `from` to `qed simp_all`;
#   g's `obtain` also fixes `x`;  i shares 17 with `moreover`;  j runs from
#   its `then` (19) to 20;  k is 21;  m, n are one `define` (22);  p is a
#   statement premise.
SPANS = r'''theory Spans
  imports Main
begin

lemma spans: "True"
proof -
  have a: "True"
    by simp
  have b: "True" by simp have c: "True" by simp
  have d: "True" and e: "True" by simp
  from TrueI have f: "True"
  proof -
    show ?thesis by simp
  qed simp_all
  obtain x :: nat where g: "x = x" by simp
  have "True" by simp
  moreover have i: "True" by simp
  have "True" by simp
  then
    have j: "True" by simp
  note k = TrueI
  define m n where "m = (0::nat)" and "n = (1::nat)"
  have "x = x" by simp
  show ?thesis by simp
qed

lemma premise: assumes p: "True" shows "True"
  by simp

end
'''


class Spans(_Root):
    THEORIES = {"Spans": SPANS}

    def test_exactly_the_hand_read_spans(self):
        out, code = self.run_cli("--locals", "--spans")
        rows = [ln.split(None, 4) for ln in out.splitlines()]
        self.assertEqual(code, 0)
        self.assertEqual([(r[1], r[4]) for r in rows], [
            ("a", "Spans:7..8"),
            ("b", "shares-line Spans:9..9"),
            ("c", "shares-line Spans:9..9"),
            ("d", "clause-of Spans:10..10"),
            ("e", "clause-of Spans:10..10"),
            ("f", "Spans:11..14"),
            ("g", "binds-vars Spans:15..15"),
            ("i", "shares-line Spans:17..17"),
            ("j", "Spans:19..20"),
            ("k", "Spans:21..21"),
            ("m", "clause-of Spans:22..22"),
            ("n", "clause-of Spans:22..22"),
            ("p", "premise"),
        ])

    def test_a_span_is_the_locus_grammar(self):
        # `lines` takes the span as printed: it is input as well as output.
        out, _ = self.run_cli("--locals", "--spans")
        span = out.splitlines()[5].split()[-1]
        self.assertEqual(span, "Spans:11..14")
        self.assertIsNotNone(cli._parse_locus(span))

    def test_spans_need_locals(self):
        self.assertEqual(self.run_cli("--spans")[1], 2)

    def test_without_the_flag_the_rows_are_unchanged(self):
        out, _ = self.run_cli("--locals")
        self.assertEqual(out.splitlines()[0].split(),
                         ["Spans:7", "a", "have", "spans"])


EXTENT = r'''theory Extent
  imports Main
begin

lemma before: "True"
proof -
  have u: "True" by simp
  show ?thesis using u by simp
qed

instance nat :: foo
proof
  have v: "True" by simp
  show "True" by simp
qed

lemma sub: "True \<and> True"
  apply (rule conjI)
  subgoal by simp
  subgoal proof -
    have w: "True" by simp
    show ?thesis by simp
  qed
  done

lemma remark: "True"
proof -
  have x: "True" by simp
  text \<open>A remark in the middle of a proof.\<close>
  show ?thesis using x by simp
qed

lemma prose_decl: "True"
proof -
  have y: "True" by simp
  text \<open>As in
lemma foo, which this mirrors.\<close>
  show ?thesis using y by simp
qed

end
'''


class Extent(_Root):
    """The walk stops where the entry's OWN proof does — neither at the first
    `text` block (`body_end_line`) nor at the next entry (`thy_end`)."""
    THEORIES = {"Extent": EXTENT}

    def entry(self, name):
        sec = self.sections[0]
        return sec, next(e for e in sec.entries if e.name == name)

    def test_a_following_instance_proof_is_not_the_lemmas(self):
        # `v` is unread, but it is the `instance`'s, which is no entry: it
        # must not be reported as a binding of `before`.
        self.assertEqual(proof_locals.proof_end(*self.entry("before")), 9)
        self.assertNotIn("v", [r[1] for r in self.unread()])

    def test_an_apply_script_runs_past_its_subgoals(self):
        self.assertEqual(proof_locals.proof_end(*self.entry("sub")), 24)
        self.assertIn((21, "w", "have", "sub"), self.unread())

    def test_a_text_block_does_not_end_the_proof(self):
        self.assertEqual(proof_locals.proof_end(*self.entry("remark")), 31)
        # [body-end-text]: the parser's own extent agrees, where it used to
        # stop at the `text` on line 29.
        self.assertEqual(self.entry("remark")[1].body_end_line, 31)

    def test_prose_in_a_text_block_is_not_a_declaration(self):
        # Line 37 begins with `lemma`, inside the block: English, not the next
        # entry (`Kyber_gpv_IND_CPA:273` has exactly this).
        self.assertEqual(self.entry("prose_decl")[1].body_end_line, 39)

    def test_parser_and_walk_agree_on_where_proofs_close(self):
        # Two walks of one structure: `parsing` (for `body_end_line`) and
        # `proof_locals` (which also tracks names).  They must not drift.
        from isabelle_query.parsing import _proof_close_line
        sec = self.sections[0]
        outer = sec.outer_source()
        for e in sec.entries:
            if e.proof_line:
                with self.subTest(entry=e.name):
                    self.assertEqual(
                        _proof_close_line(outer, e.proof_line, e.thy_end),
                        proof_locals.proof_end(sec, e))


if __name__ == "__main__":
    unittest.main()
