"""Shape step scanner — classification, nesting depth, and statement spans.

The shape metrics attach to individual Isar *steps*, which the base parser
does not model.  `shape._scan_steps` adds that: it walks a proof body and
classifies each live command line (goal / context / plumbing / closing) with
its proof-block nesting depth, extracting the proposition span for goal steps.

The fixture (`Shape.thy`) is hand-computed: a flat `by` proof, a `chained`
proof exercising the plumbing-prefixed goal forms (`from a have`, `moreover
have`, `ultimately show`), and a `nested` proof with a second `proof … qed`
level plus `fix` / `assume` context steps.  Every expected value below is
read off the fixture source by hand, not from the implementation.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import cli, needs_hol_methods, section_from  # noqa: E402
from isabelle_query import graph, shape  # noqa: E402

FIXTURES = os.path.join(os.path.dirname(__file__), "fixtures")
with open(os.path.join(FIXTURES, "Shape.thy"), encoding="utf-8") as _fh:
    THY = _fh.read()


def _sec():
    return section_from(THY, "Shape")


def _entry(sec, name):
    return next(e for e in sec.entries if e.name == name)


def _steps(name):
    sec = _sec()
    return shape._scan_steps(sec, _entry(sec, name))


def _annotated(name):
    """Steps with M5a fan-in annotated."""
    sec = _sec()
    steps = shape._scan_steps(sec, _entry(sec, name))
    shape.annotate_fanin(steps, sec)
    return steps


def _shape(steps):
    """(line, depth, kw, kind) per step — the classification skeleton."""
    return [(s.line, s.depth, s.kw, s.kind) for s in steps]


class ClassifyLine(unittest.TestCase):
    """`_classify_step_line` keys on the command prefix (before the first
    proposition), so a plumbing-prefixed goal is still a goal."""

    def test_bare_goal(self):
        self.assertEqual(shape._classify_step_line('have "P" by simp'), "goal")

    def test_plumbing_prefixed_goal(self):
        # `from a have b: "P"` — plumbing leads, but the `have` in the prefix
        # makes it a goal step.
        self.assertEqual(shape._classify_step_line('from a have b: "P"'), "goal")
        self.assertEqual(
            shape._classify_step_line('ultimately show "Q" by blast'), "goal")

    def test_context(self):
        self.assertEqual(shape._classify_step_line("fix y"), "context")
        self.assertEqual(shape._classify_step_line('assume "y = y"'), "context")

    def test_plumbing(self):
        self.assertEqual(shape._classify_step_line("moreover"), "plumbing")
        self.assertEqual(shape._classify_step_line("using a b"), "plumbing")

    def test_closing(self):
        self.assertEqual(shape._classify_step_line("by simp"), "closing")
        self.assertEqual(shape._classify_step_line("done"), "closing")
        self.assertEqual(shape._classify_step_line(".."), "closing")

    def test_structural_is_other(self):
        # `proof` / `qed` / `{` / `next` govern block structure but are not steps
        # (qed is re-classified as a closing step inside the scanner, by line).
        self.assertEqual(shape._classify_step_line("proof -"), "other")
        self.assertEqual(shape._classify_step_line("next"), "other")
        self.assertEqual(shape._classify_step_line("{"), "other")

    def test_goal_keyword_inside_a_term_does_not_count(self):
        # `have` appears only inside the proposition, not the command prefix.
        self.assertEqual(
            shape._classify_step_line('show "collect_have x = y"'), "goal")
        # The leading command is still `show` (goal); the point is that a line
        # whose *only* `have` is inside quotes is not misread — here the check is
        # that a bare fact-plumbing line with a quoted term stays plumbing:
        self.assertEqual(
            shape._classify_step_line('note x = "no have here"'), "plumbing")

    def test_unfolding_is_a_step_keyword_like_using(self):
        # `unfolding` is a proof command — Isabelle's own keyword kind for it is
        # `prf_decl`, the same kind as `using` — so it leads a step exactly as
        # `using` does, whether or not a terminal method follows it on the line.
        #
        # It did not, and a standalone `unfolding` line scanned to nothing:
        # 5,600 lost steps over the 685 theories `probe_step_alignment.py`
        # compares against Isabelle's `PIDE/markup` [markup-step-model].  The
        # two spellings were also inconsistent with each other, which is what
        # made the gap easy to miss — `using X by simp` was plumbing while
        # `unfolding X by simp` was closing.
        for line in ("unfolding foo_def",
                     "unfolding foo_def by simp",
                     "unfolding a b ..",
                     "unfolding Foo.bar_def"):
            self.assertEqual(shape._classify_step_line(line), "plumbing", line)
        # …and `using` reads the same way in every one of those shapes.
        for line in ("using a", "using a by auto", "using a ..",
                     "using Foo.bar"):
            self.assertEqual(shape._classify_step_line(line), "plumbing", line)

    def test_unknown_head_with_a_terminal_method_is_closing(self):
        # The fallback that remains: a line led by a fact name or by a word the
        # classifier does not know, but carrying a terminal method, still closes.
        self.assertEqual(shape._classify_step_line("foo_def by simp"), "closing")
        self.assertEqual(shape._classify_step_line("foo bar .."), "closing")
        # A single `.` from a dotted fact name must NOT read as the `.` closer.
        self.assertEqual(shape._classify_step_line("Foo.bar_def"), "other")


class FlatProof(unittest.TestCase):
    def test_only_the_closing_step(self):
        # `lemma flat_proof: "True" by simp` (proof on its own line 6): a flat
        # proof has no in-proof goal steps, just the closing `by`.
        self.assertEqual(_shape(_steps("flat_proof")),
                         [(6, 0, "by", "closing")])

    def test_single_line_unfolding_by_is_one_step(self):
        # Regression: a proof that is a lone `unfolding ... by` line must scan to
        # one step (so `analyze_proof` returns a record) rather than zero (which
        # drops the entry).  `bar` follows so `foo`'s span is naturally bounded —
        # the gap is in step classification, not the span.
        thy = ('theory T imports Main begin\n'
               'lemma foo: "True"\n'
               '  unfolding refl by simp\n'
               'lemma bar: "True"\n'
               '  by simp\n'
               'end\n')
        sec = section_from(thy, "T")
        foo = _entry(sec, "foo")
        self.assertEqual([(s.kind, s.kw) for s in shape._scan_steps(sec, foo)],
                         [("plumbing", "unfolding")])
        self.assertIsNotNone(shape.analyze_proof(sec, foo))

    def test_standalone_unfolding_line_is_its_own_step(self):
        # [markup-step-model]: `unfolding` on a line of its own is a command
        # Isabelle counts (kind `prf_decl`) and `query` did not — the proof
        # scanned to ONE step where Isabelle marks two.  Hand-computed from
        # `DitherTM:155`, whose shape this reproduces.
        thy = ('theory T imports Main begin\n'
               'lemma foo: "True"\n'
               '  unfolding refl\n'
               '  by simp\n'
               'lemma bar: "True"\n'
               '  by simp\n'
               'end\n')
        sec = section_from(thy, "T")
        self.assertEqual(
            [(s.line, s.kind, s.kw)
             for s in shape._scan_steps(sec, _entry(sec, "foo"))],
            [(3, "plumbing", "unfolding"), (4, "closing", "by")])


class ChainedProof(unittest.TestCase):
    def test_step_shape(self):
        self.assertEqual(_shape(_steps("chained")), [
            (12, 0, "from", "goal"),
            (13, 0, "moreover", "goal"),
            (14, 0, "ultimately", "goal"),
            (15, 0, "qed", "closing"),
        ])

    def test_goal_statements_and_labels(self):
        goals = [s for s in _steps("chained") if s.kind == "goal"]
        self.assertEqual([g.stmt_text for g in goals],
                         ["P", "P", "P \\<and> P"])
        # only `from a have p1:` carries a label
        self.assertEqual([g.label for g in goals], ["p1", "", ""])


class NestedProof(unittest.TestCase):
    def test_step_shape_and_depth(self):
        # The lemma's own `proof` is depth-0 scaffolding; the second `proof`
        # nests fix/assume/show to depth 1.
        self.assertEqual(_shape(_steps("nested")), [
            (20, 0, "have", "goal"),
            (22, 1, "fix", "context"),
            (23, 1, "assume", "context"),
            (24, 1, "show", "goal"),
            (25, 1, "qed", "closing"),
            (26, 0, "show", "goal"),
            (27, 0, "qed", "closing"),
        ])

    def test_goal_statements(self):
        goals = [s for s in _steps("nested") if s.kind == "goal"]
        self.assertEqual([g.stmt_text for g in goals],
                         ["x = x", "x = x", "x = x"])
        self.assertEqual([g.line for g in goals], [20, 24, 26])
        self.assertEqual(goals[0].label, "outer")


class W2SrcTokeniser(unittest.TestCase):
    """`_stmt_tokens` — one token per identifier/symbol run or punctuation char;
    an Isabelle `\\<sym>` and a glued sub/superscript stay a single token."""

    def test_plain(self):
        self.assertEqual(shape._stmt_tokens("x = x"), ["x", "=", "x"])

    def test_symbol_is_one_token(self):
        self.assertEqual(shape._stmt_tokens("P \\<and> P"),
                         ["P", "\\<and>", "P"])

    def test_glued_subscript_stays_attached(self):
        self.assertEqual(shape._stmt_tokens("f x = g\\<^sub>1 y"),
                         ["f", "x", "=", "g\\<^sub>1", "y"])

    def test_delimiters_each_count(self):
        self.assertEqual(shape._stmt_tokens("(a + b)"),
                         ["(", "a", "+", "b", ")"])


class W2Src(unittest.TestCase):
    """M2 headline: token count of a goal step's as-written proposition."""

    def test_chained_goal_widths(self):
        goals = [s for s in _steps("chained") if s.kind == "goal"]
        self.assertEqual([shape.w2_src(g) for g in goals], [1, 1, 3])

    def test_nested_goal_widths(self):
        goals = [s for s in _steps("nested") if s.kind == "goal"]
        self.assertEqual([shape.w2_src(g) for g in goals], [3, 3, 3])

    def test_non_goal_steps_are_zero(self):
        # context / plumbing / closing steps have no proposition to measure.
        non_goals = [s for s in _steps("nested") if s.kind != "goal"]
        self.assertTrue(all(shape.w2_src(s) == 0 for s in non_goals))


class FanIn(unittest.TestCase):
    """M5a: distinct facts cited for each goal step (own line + preceding
    plumbing lines that serve it)."""

    def _goal_fanins(self, name):
        return [s.fanin for s in _annotated(name) if s.kind == "goal"]

    def test_chained(self):
        # from a -> {a}; using a -> {a}; (rule conjI) -> {conjI}
        self.assertEqual(self._goal_fanins("chained"), [1, 1, 1])

    def test_nested(self):
        # have outer: cites nothing; show by simp nothing; (rule outer) -> {outer}
        self.assertEqual(self._goal_fanins("nested"), [0, 0, 1])

    def test_standalone_plumbing_line_attaches_to_next_goal(self):
        # `from h` on its own line serves `have step: ... by assumption`, so that
        # goal's fan-in is {h}; the following `then show ... by blast` cites no
        # explicit fact (the `then` chains `this` implicitly — that is M5b).
        self.assertEqual(self._goal_fanins("standalone"), [1, 0])

    def test_flat_proof_has_no_goal_steps(self):
        self.assertEqual(self._goal_fanins("flat_proof"), [])


class CitationDirection(unittest.TestCase):
    r"""M5a: WHICH goal a standalone plumbing line serves.

    Isar splits the plumbing keywords by proof mode, and the two halves point in
    opposite directions.  `from` / `with` / `then` / `moreover` / `ultimately`
    run in `proof(state)` — before a goal is stated — so they chain forward into
    the next one.  `using` / `unfolding` are legal only in `proof(prove)` —
    after a goal is stated, before its method — so they cite backward, for the
    goal already open.

    Every value below is read off the source by hand.  The fixture is written so
    that a direction error cannot pass: each goal cites a DIFFERENT fact, so
    crediting the wrong goal produces the wrong list rather than the same
    multiset in a different order (which `[1, 1]` would not have caught).
    """

    THY = ('theory T imports Main begin\n'                    # 1
           'lemma a1: "True" by simp\n'                       # 2
           'lemma a2: "True" by simp\n'                       # 3
           'lemma r: "True"\n'                                # 4
           'proof -\n'                                        # 5
           '  have p: "True"\n'                               # 6
           '    using a1 by simp\n'                           # 7
           '  have q: "True"\n'                               # 8
           '    unfolding a2 by simp\n'                       # 9
           '  from p show "True" by blast\n'                  # 10
           'qed\n'                                            # 11
           'end\n')                                           # 12

    def _annotated(self):
        sec = section_from(self.THY, "T")
        entry = next(e for e in sec.entries if e.name == "r")
        steps = shape._scan_steps(sec, entry)
        shape.annotate_fanin(steps, sec)
        return sec, steps

    def test_using_and_unfolding_credit_the_goal_above(self):
        # `have p` is served by line 7's `using a1`  -> 1
        # `have q` is served by line 9's `unfolding a2` -> 1
        # `from p show` cites `p` on its own line       -> 1
        # Before the fix these read [0, 1, 1]: a1 was credited to `q` and a2 to
        # the `show`, so the total was right and every attribution was wrong.
        _sec_, steps = self._annotated()
        self.assertEqual([(s.line, s.fanin)
                          for s in steps if s.kind == "goal"],
                         [(6, 1), (8, 1), (10, 1)])

    def test_forward_chain_still_serves_the_next_goal(self):
        # The `from`/`with` half must not move: a standalone `from` line before
        # a goal still attaches to it.  (`Shape.thy`'s `standalone` proof is the
        # fixture for that; this is the guard that the split did not swap them.)
        self.assertEqual(
            [s.fanin for s in _annotated("standalone") if s.kind == "goal"],
            [1, 0])

    def test_a_backward_cite_with_no_open_goal_is_dropped(self):
        # A `using` line that no goal precedes (the whole proof is
        # `using x by simp`) has nothing to credit.  It must not fall back to
        # the forward chain and land on a later goal — undercount, never
        # misattribute.
        thy = ('theory T imports Main begin\n'
               'lemma a1: "True" by simp\n'
               'lemma r: "True"\n'
               '  using a1 by simp\n'
               'end\n')
        sec = section_from(thy, "T")
        entry = next(e for e in sec.entries if e.name == "r")
        steps = shape._scan_steps(sec, entry)
        shape.annotate_fanin(steps, sec)
        self.assertEqual([(s.line, s.kind, s.fanin) for s in steps],
                         [(4, "plumbing", 0)])


def _live(name):
    sec = _sec()
    steps = shape._scan_steps(sec, _entry(sec, name))
    return shape.live_fact_space(steps, sec)


def _ic(name):
    sec = _sec()
    steps = shape._scan_steps(sec, _entry(sec, name))
    return shape.introduce_consume(steps, sec)


class Introduces(unittest.TestCase):
    """M5c introduce flag keys on the goal command, not the leading keyword."""

    def _by_line(self, name):
        return {s.line: (shape.introduces(s), s.goal_cmd) for s in _steps(name)}

    def test_from_have_introduces_via_goal_cmd(self):
        # `from a have p1:` leads with plumbing (kw="from") but binds `p1`.
        flags = self._by_line("chained")
        self.assertEqual(flags[12], (True, "have"))
        # `ultimately show` discharges — goal_cmd="show", not an introducer.
        self.assertEqual(flags[14], (False, "show"))

    def test_context_and_closing(self):
        flags = self._by_line("nested")
        self.assertEqual(flags[20][0], True)    # have outer:
        self.assertEqual(flags[22][0], False)   # fix y — a variable, not a fact
        self.assertEqual(flags[23][0], True)    # assume "y = y"
        self.assertEqual(flags[26], (False, "show"))
        self.assertEqual(flags[27][0], False)   # qed


class LiveFactSpace(unittest.TestCase):
    """M5b: peak and mean simultaneously-live named facts."""

    def test_reuse_holds_three_at_the_peak(self):
        # f1[L42..show], f2[L43..f3], f3[L44..show] — all three coexist at L44
        # (`have f3: ... using f1 f2`).  live per step: 1,2,3,2,0 -> max 3.
        self.assertEqual(_live("reuse"), (3, 1.6))

    def test_standalone_then_chaining_extends_life(self):
        # `step` is introduced at L34 and consumed by the implicit `this` of
        # `then show` at L35, so it lives across two of the four steps.
        self.assertEqual(_live("standalone"), (1, 0.5))

    def test_nested_single_fact_peak(self):
        # Only `outer` is a named in-proof fact -> peak 1.  (Mean is left
        # unpinned: the flat birth-at-statement model counts `outer` live during
        # its own sub-proof, a documented over-approximation of the mean.)
        self.assertEqual(_live("nested")[0], 1)

    def test_flat_proof_is_empty(self):
        self.assertEqual(_live("flat_proof"), (0, 0.0))


class IntroduceConsume(unittest.TestCase):
    """M5c: introducing / consuming line tallies and their three-way split."""

    def test_chained(self):
        ic = _ic("chained")
        # L12 both, L13 both, L14 consume-only (rule conjI), L15 qed neither.
        self.assertEqual(
            (ic.introduce, ic.consume, ic.both), (2, 3, 2))
        self.assertEqual(
            (ic.introduce_only, ic.consume_only, ic.neither), (0, 1, 1))
        self.assertEqual(ic.ratio, 2 / 3)

    def test_standalone(self):
        ic = _ic("standalone")
        # L33 `from h` consume-only, L34 `have step:` introduce-only,
        # L35 `then show` neither (implicit this is not explicit citation),
        # L36 qed neither.
        self.assertEqual(
            (ic.introduce_only, ic.consume_only, ic.both), (1, 1, 0))
        self.assertEqual(ic.ratio, 1.0)

    def test_nested(self):
        ic = _ic("nested")
        # introduce: L20 have outer, L23 assume; consume: L26 rule outer.
        self.assertEqual((ic.introduce, ic.consume), (2, 1))
        self.assertEqual(ic.ratio, 2.0)

    def test_reuse(self):
        ic = _ic("reuse")
        # three `have ... using` (both) + one `show ... using` (consume-only).
        self.assertEqual((ic.introduce, ic.consume, ic.both), (3, 4, 3))
        self.assertEqual((ic.consume_only, ic.neither), (1, 1))
        self.assertEqual(ic.ratio, 0.75)

    def test_flat_proof_ratio_is_undefined(self):
        # A bare `by simp` neither introduces nor consumes -> ratio None.
        ic = _ic("flat_proof")
        self.assertEqual((ic.introduce, ic.consume), (0, 0))
        self.assertIsNone(ic.ratio)


class AnalyzeStatement(unittest.TestCase):
    """M1 token-level split: free candidates vs schematic `?vars` vs binder-bound
    names.  `_analyze_statement` is elaboration-free and deterministic."""

    def test_plain(self):
        sv = shape._analyze_statement("x = x")
        self.assertEqual((sv.free, sv.schematic, sv.bound), (("x",), (), ()))

    def test_binder_separates_bound(self):
        sv = shape._analyze_statement("\\<forall>k. P k")
        self.assertEqual(sv.bound, ("k",))
        self.assertEqual(sv.free, ("P",))      # k is bound, not free

    def test_glued_binder_prefix_is_split(self):
        # `\<exists>n` is a single glued token; the binder prefix must still bind n.
        sv = shape._analyze_statement("\\<exists>n. n = n")
        self.assertEqual((sv.bound, sv.free), (("n",), ()))

    def test_multiple_bound(self):
        sv = shape._analyze_statement("\\<lambda>x y. f x y")
        self.assertEqual((sv.bound, sv.free), (("x", "y"), ("f",)))

    def test_schematic(self):
        sv = shape._analyze_statement("?P x \\<longrightarrow> ?P x")
        self.assertEqual((sv.schematic, sv.free), (("P",), ("x",)))


class ClassifyIdentifier(unittest.TestCase):
    """The layered var/const classifier and its recorded provenance."""

    def test_context_wins_over_entry_and_corpus(self):
        ctx = shape.ClassifyCtx(entry_names=frozenset({"myconst"}),
                                context_vars=frozenset({"x", "myconst"}),
                                corpus_consts=frozenset({"rev"}))
        # a `fix`/`for` binding shadows a global of the same name.
        self.assertEqual(shape.classify_identifier("myconst", ctx),
                         ("var", "context"))
        self.assertEqual(shape.classify_identifier("rev", ctx),
                         ("const", "corpus"))
        self.assertEqual(shape.classify_identifier("if", ctx),
                         ("const", "syntax"))

    def test_entry_then_default(self):
        # The fixture name must be outside the syntax table, which is checked
        # BEFORE the entry bucket: `foo` was used here and is a real registered
        # method in the HOL-family union (as are `all`, `catch`, `apply_A`), so it
        # took the `syntax` bucket and this stopped testing entry-vs-default the
        # moment that union became the default table.
        ctx = shape.ClassifyCtx(entry_names=frozenset({"myentry"}),
                                corpus_consts=frozenset())
        self.assertEqual(shape.classify_identifier("myentry", ctx),
                         ("const", "entry"))
        self.assertEqual(shape.classify_identifier("y", ctx), ("var", "default"))

    def test_syntax_wins_over_entry(self):
        # …and the precedence that displaced it, pinned on purpose: a name in the
        # bound table is `syntax` even when an entry declares it.
        ctx = shape.ClassifyCtx(entry_names=frozenset({"foo"}),
                                corpus_consts=frozenset())
        self.assertIn("foo", graph._PROOF_METHODS)   # premise, not an assumption
        self.assertEqual(shape.classify_identifier("foo", ctx),
                         ("const", "syntax"))

    def test_single_letter_constant_misclassifies(self):
        # An algebra identity `e` is a CONSTANT, but with no fix / entry / HOL
        # evidence it falls to `default` -> var.  This is the documented estimator
        # weakness (single-letter constants); w1_est over-counts as a result.
        ctx = shape.ClassifyCtx()
        self.assertEqual(shape.classify_identifier("e", ctx), ("var", "default"))
        sv = shape._analyze_statement("x \\<otimes> e = x")
        self.assertEqual(sv.free, ("x", "e"))   # both counted -> w1_est = 2


class W1Est(unittest.TestCase):
    """M1 estimator through the full per-lemma pipeline (`build_ctx` + `w1_est`)."""

    def _goal_w1s(self, name):
        sec = _sec()
        entry = _entry(sec, name)
        steps = shape._scan_steps(sec, entry)
        ctx = shape.build_ctx(sec, entry, steps)
        return [shape.w1_est(s, ctx) for s in steps if s.kind == "goal"]

    def test_classify_demo(self):
        have, show = self._goal_w1s("classify_demo")
        # have step: "\<forall>k. rev [g, k] = rev [g, k]"
        #   g -> var (fixes g), rev -> const (HOL), k -> bound.
        self.assertEqual((have.free, have.schematic, have.bound), (1, 0, 1))
        self.assertEqual(have.free_names, ("g",))
        self.assertEqual(have.provenance["rev"], ("const", "corpus"))
        self.assertEqual(have.provenance["g"], ("var", "context"))
        # show "rev [g] = rev [g]" — one free var (g), no binder.
        self.assertEqual((show.free, show.schematic, show.bound), (1, 0, 0))

    def test_default_vars_without_fixes(self):
        # reuse has no `fixes`; the uppercase prop vars fall to default -> var.
        self.assertEqual([w.free for w in self._goal_w1s("reuse")], [1, 1, 2, 2])

    def test_corpus_list_has_staples(self):
        for c in ("Suc", "map", "rev", "length", "insert", "finite", "set"):
            self.assertIn(c, shape.CORPUS_CONSTANTS)

    def test_fix_line_does_not_leak_proposition_constants(self):
        # `fix VS assume "..."` on one line: only the leading `VS` is a bound
        # variable; the trailing proposition's constants (`insert`) must NOT be
        # captured as context vars (regression — they used to leak and then get
        # misclassified as variables).
        thy = ('theory T imports Main begin\n'
               'lemma l: shows "True"\n'
               'proof -\n'
               '  fix VS assume "VS \\<subseteq> insert a A"\n'
               '  show "True" by simp\n'
               'qed\n'
               'end\n')
        sec = section_from(thy, "T")
        entry = next(e for e in sec.entries if e.name == "l")
        steps = shape._scan_steps(sec, entry)
        cv = shape.build_ctx(sec, entry, steps).context_vars
        self.assertIn("VS", cv)
        self.assertNotIn("insert", cv)
        self.assertNotIn("A", cv)


class ConstEst(unittest.TestCase):
    """const_est — the Width vocabulary sibling of w1_est (vars) / w2_src
    (tokens): distinct constants, counting both letter-initial names tagged
    const and operator symbols written as notation."""

    def _goal_w1(self, thy, name, kw):
        sec = section_from(thy, "T")
        entry = next(e for e in sec.entries if e.name == name)
        steps = shape._scan_steps(sec, entry)
        ctx = shape.build_ctx(sec, entry, steps)
        return next(shape.w1_est(s, ctx) for s in steps
                    if s.kind == "goal" and s.kw == kw)

    def test_names_and_operator_symbols_both_count(self):
        # "Suc n + m \<le> Suc m \<and> n \<le> m": consts are the word `Suc`
        # (corpus) plus the operators `+` (ASCII), `\<le>`, `\<and>` (notation) —
        # four distinct, deduping the repeats; free vars are the fixed n, m.
        thy = ('theory T imports Main begin\n'
               'lemma mix:\n'
               '  fixes n :: nat and m :: nat\n'
               '  shows "True"\n'
               'proof -\n'
               '  have "Suc n + m \\<le> Suc m \\<and> n \\<le> m" sorry\n'
               '  show "True" by simp\n'
               'qed\n'
               'end\n')
        w = self._goal_w1(thy, "mix", "have")
        self.assertEqual((w.free, w.free_names), (2, ("n", "m")))
        self.assertEqual(w.const, 4)
        self.assertEqual(w.const_names, ("Suc", "+", "\\<le>", "\\<and>"))
        self.assertEqual(w.provenance["Suc"], ("const", "corpus"))
        # no overloaded duplicate here, so the canonical count equals const.
        self.assertEqual(w.const_canon, 4)

    def test_canonicalize_dedups_overloaded_notation(self):
        # \<le> and \<subseteq> are the same HOL constant (less_eq): const_canon
        # collapses them via the committed notation table, const_est does not.
        raw = ("\\<le>", "\\<subseteq>", "\\<and>")
        self.assertEqual(shape.NOTATION["\\<le>"], shape.NOTATION["\\<subseteq>"])
        self.assertEqual(len(shape._canonicalize_consts(raw)), 2)  # less_eq, conj
        # a word const and an un-harvested glyph both pass through unchanged.
        self.assertEqual(shape._canonicalize_consts(("insert", "\\<zzz_unknown>")),
                         ("insert", "\\<zzz_unknown>"))

    def test_is_operator_const_classification(self):
        yes = ("\\<in>", "+", "=", "\\<le>", "\\<and>", "\\<longrightarrow>")
        no = ("(", "\\<forall>",       # bracket, binder — not constants
              "\\<open>",              # cartouche bracket
              "Suc", "g\\<^sub>1",     # names (plain / subscripted)
              "\\<Gamma>", "\\<alpha>",  # Greek letter symbols — variables
              "\\<And>c_b", "\\<Union>j",  # binder glued to its bound var
              "\\<Gamma>\\<^sub>M",    # subscripted Greek-letter identifier
              "0")                     # numeral
        for t in yes:
            self.assertTrue(shape._is_operator_const(t), t)
        for t in no:
            self.assertFalse(shape._is_operator_const(t), t)


class Blocks(unittest.TestCase):
    """The scanner assigns a fresh `block` id per `proof`/`{` frame, so sibling
    blocks at the same depth are distinguishable (M4/M6 must not merge them)."""

    def test_flat_and_chained_are_one_block(self):
        self.assertEqual([s.block for s in _steps("flat_proof")], [0])
        self.assertEqual([s.block for s in _steps("chained")], [0, 0, 0, 0])

    def test_nested_second_proof_is_a_new_block(self):
        # have(0) | fix,assume,show,qed(1) | show,qed(0) — the inner proof is
        # block 1, and control returns to block 0 after its qed.
        self.assertEqual([s.block for s in _steps("nested")],
                         [0, 1, 1, 1, 1, 0, 0])


class BracketChunks(unittest.TestCase):
    """The M4/M6 chunk primitive: bracket-balanced token spans >= min length."""

    def test_tuple_is_a_chunk(self):
        toks = shape._stmt_tokens("(a, b) = (a, b)")
        self.assertEqual(shape._bracket_chunks(toks),
                         ["( a , b )", "( a , b )"])

    def test_short_group_below_threshold_is_dropped(self):
        # `( x )` is 3 tokens, below the 4-token floor -> no chunk.
        self.assertEqual(shape._bracket_chunks(shape._stmt_tokens("f (x)")), [])

    def test_nested_forest(self):
        # both the outer and the inner bracket pair are chunks.
        toks = shape._stmt_tokens("g (h (a, b))")
        self.assertEqual(shape._bracket_chunks(toks),
                         ["( a , b )", "( h ( a , b ) )"])

    def test_multiset_jaccard(self):
        self.assertEqual(shape._multiset_jaccard(["x", "x"], ["x", "y"]), 1 / 3)
        self.assertIsNone(shape._multiset_jaccard([], []))
        self.assertEqual(shape._multiset_jaccard(["x"], ["x"]), 1.0)


class CrossStepRedundancy(unittest.TestCase):
    """M4: per-block DAG compression ratio and adjacent-goal overlaps."""

    def _blocks(self, name):
        return shape.cross_step_redundancy(_steps(name))

    def test_redundant_block_compresses(self):
        # three goals, each `(a, b) = (a, b)`: 33 tokens, the tuple `( a , b )`
        # occurs 6 times (len 5) -> saves 5*5=25 -> compressed 8 -> ratio 33/8.
        (blk,) = self._blocks("redundant")
        self.assertEqual((blk.block, blk.n_goals), (0, 3))
        self.assertEqual((blk.total_tokens, blk.compressed_tokens), (33, 8))
        self.assertAlmostEqual(blk.dag_ratio, 33 / 8)
        # every adjacent pair states the identical proposition -> overlap 1.0.
        self.assertEqual(blk.overlaps, (1.0, 1.0))

    def test_framing_partial_overlap(self):
        # phi1 R(p,q)(p,q) | phi2 R(p,q)(q,p) | phi3 P(p,q).  Only `( p , q )`
        # repeats (4x, len 5) -> saves 15 -> 28/13.  Overlaps are fractional.
        (blk,) = self._blocks("framing")
        self.assertEqual((blk.total_tokens, blk.compressed_tokens), (28, 13))
        self.assertAlmostEqual(blk.dag_ratio, 28 / 13)
        self.assertAlmostEqual(blk.overlaps[0], 1 / 3)
        self.assertAlmostEqual(blk.overlaps[1], 1 / 2)

    def test_nested_two_blocks_no_redundancy(self):
        # block 0 (two `x = x`) and block 1 (one `x = x`): no brackets, so no
        # chunks -> ratio 1.0; the two chunk-free statements overlap is undefined.
        b0, b1 = self._blocks("nested")
        self.assertEqual((b0.block, b0.n_goals, b0.dag_ratio), (0, 2, 1.0))
        self.assertEqual(b0.overlaps, (None,))
        self.assertEqual((b1.block, b1.n_goals, b1.dag_ratio), (1, 1, 1.0))
        self.assertEqual(b1.overlaps, ())


class ExtensionCurveTest(unittest.TestCase):
    """M6: width-vs-k after greedily extracting repeated chunks as definitions."""

    def _curve(self, name):
        sec = _sec()
        entry = _entry(sec, name)
        steps = shape._scan_steps(sec, entry)
        ctx = shape.build_ctx(sec, entry, steps)
        return shape.extension_curve(steps, ctx)

    def test_redundant_collapses(self):
        # k=0: raw widths (w1 = a,b per line x3 = 6; w2 = 33).  Extracting the
        # one repeated tuple removes it from every line: w1 -> 0, w2 -> 9.
        (c,) = self._curve("redundant")
        self.assertEqual(c.ks, (0, 1, 2, 4, 8, 16))
        self.assertEqual(c.w1, (6, 0, 0, 0, 0, 0))
        self.assertEqual(c.w2, (33, 9, 9, 9, 9, 9))

    def test_framing_partial(self):
        # Only `( p , q )` is extracted; the once-only `( q , p )` in phi2
        # survives, so width does not collapse to nothing.
        (c,) = self._curve("framing")
        self.assertEqual(c.w1, (9, 5, 5, 5, 5, 5))
        self.assertEqual(c.w2, (28, 12, 12, 12, 12, 12))

    def test_k0_reproduces_raw_widths(self):
        # k=0 must equal the summed w1_est / w2_src over the block's goals.
        sec = _sec()
        entry = _entry(sec, "framing")
        steps = shape._scan_steps(sec, entry)
        ctx = shape.build_ctx(sec, entry, steps)
        goals = [s for s in steps if s.kind == "goal"]
        self.assertEqual(shape.extension_curve(steps, ctx)[0].w1[0],
                         sum(shape.w1_est(g, ctx).free for g in goals))
        self.assertEqual(shape.extension_curve(steps, ctx)[0].w2[0],
                         sum(shape.w2_src(g) for g in goals))


def _m3cfg():
    return shape.load_corpus_config(
        os.path.join(FIXTURES, "m3_configs.toml"))["Shape"]


def _goal(name):
    """The first goal step of a fixture lemma."""
    return next(s for s in _steps(name) if s.kind == "goal")


class M3ConfigLoad(unittest.TestCase):
    """M3 config is TOML, one table per corpus, loaded with stdlib tomllib."""

    def test_toml_loads_name_lists(self):
        cfg = _m3cfg()
        self.assertEqual(cfg.selectors, frozenset({"fst", "snd"}))
        self.assertEqual(cfg.constructors, frozenset({"Pair"}))
        self.assertEqual(cfg.relations, frozenset())


class FrameRatioTest(unittest.TestCase):
    """M3: mentioned = selectors + `!` + `:=`; changed = `:=`; ratio, or None."""

    def _fr(self, name):
        return shape.frame_ratio(_goal(name), _m3cfg())

    def test_pair_selectors_no_update(self):
        # `fst c = fst d \<and> snd c = snd d \<longrightarrow> c = d`
        # 4 selector accesses (fst x2, snd x2), no update -> changed 0 -> ratio 4.
        fr = self._fr("m3_pair")
        self.assertEqual((fr.mentioned, fr.changed, fr.ratio), (4, 0, 4.0))

    def test_framing_ratio_one(self):
        # `xs[0 := v] = xs[0 := v]` — every mentioned component is an update
        # (2 of them), so mentioned == changed -> ratio 1 (framing style).
        fr = self._fr("m3_framing")
        self.assertEqual((fr.mentioned, fr.changed, fr.ratio), (2, 2, 1.0))

    def test_wide_delta_tracing(self):
        # a 4-tuple of accesses restated on both sides (8 `!`) with one update
        # per side (2 `:=`): mentioned 10, changed 2 -> ratio 5 (delta-tracing).
        fr = self._fr("m3_wide")
        self.assertEqual((fr.mentioned, fr.changed, fr.ratio), (10, 2, 5.0))

    def test_non_config_proposition_is_null(self):
        cfg = _m3cfg()
        # "x = x" is a relation but mentions no configured component.
        self.assertIsNone(shape.frame_ratio(_goal("nested"), cfg))
        # "P" is not even a relation.
        self.assertIsNone(shape.frame_ratio(_goal("chained"), cfg))


class M3SummaryTest(unittest.TestCase):
    """M3 aggregate: computed ratios + coverage (every goal step in the
    denominator, only configuration relations in the numerator)."""

    def _sum(self, name):
        return shape.frame_ratios(_steps(name), _m3cfg())

    def test_wide_full_coverage(self):
        s = self._sum("m3_wide")
        self.assertEqual((s.n_goals, s.n_computed, s.coverage), (1, 1, 1.0))
        self.assertEqual((s.max_ratio, s.mean_ratio), (5.0, 5.0))

    def test_nested_zero_coverage(self):
        # three `x = x` goals, none a configuration relation -> coverage 0.
        s = self._sum("nested")
        self.assertEqual((s.n_goals, s.n_computed, s.coverage), (3, 0, 0.0))
        self.assertIsNone(s.max_ratio)


def _pm(name):
    """The composed ProofMetrics for a fixture lemma."""
    sec = _sec()
    return shape.analyze_proof(sec, _entry(sec, name))


class AnalyzeProof(unittest.TestCase):
    """`analyze_proof` runs the per-proof pipeline once, in dependency order
    (fan-in / live annotation before any per-step record).  The redundant lemma
    (`(a, b) = (a, b)` x3) is fully hand-computed."""

    def test_bare_definition_has_no_metrics(self):
        # flat_proof is `by simp` — one closing step, no goals.  It still has a
        # step, so analyze_proof is not None; its rollup has zero goals.
        pm = _pm("flat_proof")
        self.assertIsNotNone(pm)
        self.assertEqual(pm.goals, [])

    def test_annotation_ran_before_access(self):
        # fan-in and live are set on the steps by the pipeline, not left 0.
        pm = _pm("reuse")
        # `show ... using f3 f1` — fan-in 2 — is the last goal.
        self.assertEqual(pm.goals[-1].fanin, 2)
        self.assertEqual(pm.live_max, 3)   # matches the M5b test's peak

    def test_redundant_rollup_is_hand_computed(self):
        ps = shape.summarize(_pm("redundant"))
        # steps: have s1 | have s2 | show | qed  (3 goals, 0 bare).
        self.assertEqual((ps.n_steps, ps.n_goals, ps.n_bare), (4, 3, 0))
        # flat proof (every step in the lemma's own `proof`) -> depth 1.
        self.assertEqual(ps.depth_max, 1)
        # each goal is `(a, b) = (a, b)` = 11 tokens.
        self.assertEqual((ps.w2_max, ps.w2_mean, ps.w2_p90), (11, 11.0, 11.0))
        # free vars a, b (both `fixes`) -> w1_est 2 per goal.
        self.assertEqual((ps.w1_max, ps.w1_mean), (2, 2.0))
        # only `show ... using s1 s2` cites -> fan-in [0, 0, 2].
        self.assertEqual(ps.fanin_max, 2)
        self.assertAlmostEqual(ps.fanin_mean, 2 / 3)
        # one of three goals cites -> fanin_cited 1 (conditional fan-in = 2/1).
        self.assertEqual(ps.fanin_cited, 1)
        # s1[L60..show], s2[L61..show] coexist at the show -> live peak 2.
        self.assertEqual(ps.live_max, 2)
        self.assertAlmostEqual(ps.live_mean, 1.25)
        # the one block's M4 ratio (33 tokens / 8 compressed).
        self.assertAlmostEqual(ps.dag_max, 33 / 8)
        # introduce s1, s2 (show discharges); consume the one `using` line;
        # no line both introduces and cites -> both 0.
        self.assertEqual((ps.intro, ps.consume, ps.both, ps.ratio), (2, 1, 0, 2.0))
        # all three discharges are `by simp` -> trivial_frac 1.0.
        self.assertEqual(ps.trivial_frac, 1.0)
        # the block's `( a , b )` chunk (6 occurrences) collapses each of the 3
        # statements 11 -> 3 tokens: 33 -> 9, so 1 - 9/33 removable.
        self.assertAlmostEqual(ps.removable_w2, 1 - 9 / 33)


class DepthMax(unittest.TestCase):
    """`ProofSummary.depth_max` — max proof-block nesting, 1-based (1 = a flat
    proof), the 2015 mining paper's proof-depth axis (= max step `depth` + 1).
    Hand-computed from each fixture's `proof … qed` structure."""

    def _depth(self, name):
        return shape.summarize(_pm(name)).depth_max

    def test_flat_one_liner_is_depth_1(self):
        # `flat_proof` is `by simp` — one closing step at depth 0.
        self.assertEqual(self._depth("flat_proof"), 1)

    def test_flat_structured_proof_is_depth_1(self):
        # `chained`: three steps all in the lemma's own `proof -`, no nesting.
        self.assertEqual(self._depth("chained"), 1)

    def test_one_nested_block_is_depth_2(self):
        # `nested`: the inner `proof -` puts fix/assume/show at step-depth 1.
        self.assertEqual(self._depth("nested"), 2)

    def test_two_nested_blocks_is_depth_3(self):
        # `deeply_nested`: two nested `proof -` blocks -> deepest step-depth 2.
        self.assertEqual(self._depth("deeply_nested"), 3)

    def test_summary_record_carries_depth_max(self):
        rec = shape.summary_record(shape.summarize(_pm("nested")))
        self.assertEqual(rec["depth_max"], 2)


class FanInCited(unittest.TestCase):
    """`ProofSummary.fanin_cited` — the count of goal steps citing >=1 explicit
    premise: the denominator that turns the (over-all-goals) `fanin_mean` into
    the *conditional* fan-in (the mean over goal steps that cite ≥1).
    Hand-computed from each fixture's goal fan-ins."""

    def _cited(self, name):
        return shape.summarize(_pm(name)).fanin_cited

    def test_every_goal_cites(self):
        # reuse: goal fan-ins [1, 1, 2, 2] -> all four cite.
        self.assertEqual(self._cited("reuse"), 4)
        # chained: [1, 1, 1] -> all three cite.
        self.assertEqual(self._cited("chained"), 3)

    def test_only_citing_goals_counted(self):
        # nested: [0, 0, 1] and standalone: [1, 0] -> one citing goal each.
        self.assertEqual(self._cited("nested"), 1)
        self.assertEqual(self._cited("standalone"), 1)

    def test_goal_free_proof_is_zero(self):
        # flat_proof `by simp` has no goal steps -> nothing cites.
        self.assertEqual(self._cited("flat_proof"), 0)

    def test_summary_record_carries_fanin_cited(self):
        rec = shape.summary_record(shape.summarize(_pm("reuse")))
        self.assertEqual(rec["fanin_cited"], 4)


class TrivialAndRemovable(unittest.TestCase):
    """`Step.method`, `trivial_frac`, and the M6 `removable_w2_at_8` scalar —
    the two additions that make the census record a sufficient statistic."""

    def _methods(self, name):
        """The discharge method of each step that has one, in source order."""
        pm = _pm(name)
        return [s.method for s in pm.steps if s.method]

    @needs_hol_methods
    def test_method_is_the_leading_discharge(self):
        # redundant: three `by simp` goals; `qed` carries no method.
        self.assertEqual(self._methods("redundant"), ["simp", "simp", "simp"])
        # chained mixes a bracketed method: `by (rule conjI)` -> "rule".
        self.assertEqual(self._methods("chained"), ["blast", "simp", "rule"])
        # m3_pair: `by (auto simp: ...)` -> the leading method "auto".
        self.assertEqual(self._methods("m3_pair"), ["auto"])

    @needs_hol_methods
    def test_trivial_frac_over_methoded_steps(self):
        # redundant / reuse: every discharge is `simp` -> 1.0.
        self.assertEqual(shape.trivial_frac(_pm("redundant").steps), 1.0)
        self.assertEqual(shape.trivial_frac(_pm("reuse").steps), 1.0)
        # chained: {blast, simp} trivial of {blast, simp, rule} -> 2/3.
        self.assertAlmostEqual(shape.trivial_frac(_pm("chained").steps), 2 / 3)
        # nested: {simp} trivial of {simp, rule} -> 0.5.
        self.assertEqual(shape.trivial_frac(_pm("nested").steps), 0.5)

    def test_trivial_frac_none_when_no_method(self):
        # A body whose steps carry no `by`/`apply` on their own line discharges
        # nothing measurably -> undefined, not 0.  (Construct such a step list.)
        steps = [shape.Step("T", "l", 1, 0, "have", "goal", method="")]
        self.assertIsNone(shape.trivial_frac(steps))

    def test_removable_scalar(self):
        # redundant: 1 - 9/33 (the `(a, b)` chunk collapses each statement).
        pm = _pm("redundant")
        self.assertAlmostEqual(
            shape.removable_w2_at_8(pm.steps, pm.ctx), 1 - 9 / 33)
        # nested: `x = x` statements have no bracket chunks -> nothing removable.
        pm = _pm("nested")
        self.assertEqual(shape.removable_w2_at_8(pm.steps, pm.ctx), 0.0)


class MethodKinds(unittest.TestCase):
    """The method-kind taxonomy — the automation axis's finer grain than the
    binary `trivial_frac`."""

    def test_classification(self):
        self.assertEqual(shape.method_kind("simp"), "automation")
        self.assertEqual(shape.method_kind("blast"), "search")
        self.assertEqual(shape.method_kind("linarith"), "arith")
        self.assertEqual(shape.method_kind("induct"), "structural")
        # a recognised method outside the four core families -> "other".
        self.assertEqual(shape.method_kind("transfer"), "other")
        self.assertEqual(shape.method_kind(""), "")          # not discharged

    @needs_hol_methods
    def test_counts_partition_discharged_steps(self):
        # chained discharges blast / simp / rule -> search / automation /
        # structural (one each); the counts partition the discharged steps.
        c = shape.method_kind_counts(_pm("chained").steps)
        self.assertEqual(c, {"automation": 1, "search": 1, "arith": 0,
                             "structural": 1, "other": 0})
        self.assertEqual(set(c), set(shape.METHOD_KIND_NAMES))   # uniform keys
        # sum == discharged steps == the trivial_frac denominator.
        self.assertEqual(sum(c.values()),
                         len([s for s in _pm("chained").steps if s.method]))

    def test_counts_over_redundant(self):
        # redundant: three `by simp` -> all automation.
        c = shape.method_kind_counts(_pm("redundant").steps)
        self.assertEqual((c["automation"], sum(c.values())), (3, 3))


class StepRecord(unittest.TestCase):
    """The per-step JSONL record — the join contract's field set."""

    def _records(self, name):
        pm = _pm(name)
        lines = pm.sec.source()
        return [shape.step_record(s, pm.ctx, lines) for s in pm.steps]

    def test_goal_record_fields(self):
        # redundant's `show ... using s1 s2` at L62.
        rec = next(r for r in self._records("redundant") if r["line"] == 62)
        self.assertEqual(rec["theory"], "Shape")
        self.assertEqual(rec["lemma"], "redundant")
        self.assertEqual((rec["kind"], rec["kw"], rec["goal_cmd"]),
                         ("goal", "show", "show"))
        self.assertEqual(rec["method"], "simp")   # `... using s1 s2 by simp`
        self.assertEqual(rec["block"], 0)
        self.assertEqual(rec["w2_src"], 11)
        self.assertEqual(rec["w1_est"], 2)
        self.assertEqual((rec["w1_schematic_est"], rec["w1_bound_est"]), (0, 0))
        self.assertEqual(rec["fanin"], 2)
        self.assertTrue(rec["fanin_covered"])
        self.assertEqual(rec["live"], 2)
        # show discharges (does not introduce) but consumes s1, s2.
        self.assertFalse(rec["introduces"])
        self.assertTrue(rec["consumes"])

    def test_estimator_columns_carry_est_suffix(self):
        # The `_est` suffix marks a token-heuristic column; the exact
        # source metrics (w2_src, fanin, live) do not carry it.
        rec = self._records("redundant")[0]
        est = {k for k in rec if k.endswith("_est")}
        self.assertEqual(est, {"w1_est", "w1_schematic_est", "w1_bound_est",
                               "const_est", "const_canon_est"})
        for exact in ("w2_src", "fanin", "live"):
            self.assertIn(exact, rec)

    def test_uniform_schema_across_step_kinds(self):
        # every step (goal / context / plumbing / closing) carries every column,
        # so the stream is a clean columnar join; non-goal metrics are just 0.
        recs = self._records("nested")
        keys = {frozenset(r) for r in recs}
        self.assertEqual(len(keys), 1)             # one schema for all steps
        qed = next(r for r in recs if r["kind"] == "closing")
        self.assertEqual((qed["w2_src"], qed["w1_est"], qed["fanin"]), (0, 0, 0))

    def test_config_gates_frame_columns(self):
        pm = _pm("m3_wide")
        lines = pm.sec.source()
        goal = next(s for s in pm.steps if s.kind == "goal")
        # without a config, no frame_* columns.
        self.assertNotIn("frame_ratio", shape.step_record(goal, pm.ctx, lines))
        # with one, the M3 columns appear (m3_wide's ratio is 5.0).
        rec = shape.step_record(goal, pm.ctx, lines, cfg=_m3cfg())
        self.assertEqual(rec["frame_ratio"], 5.0)
        self.assertEqual((rec["frame_mentioned"], rec["frame_changed"]), (10, 2))


class SummaryRecord(unittest.TestCase):
    """The per-proof JSONL record (census / summary --json)."""

    def test_matches_summarize(self):
        ps = shape.summarize(_pm("redundant"))
        rec = shape.summary_record(ps)
        self.assertEqual(rec["theory"], "Shape")
        self.assertEqual(rec["lemma"], "redundant")
        self.assertEqual((rec["n_goals"], rec["n_bare"]), (3, 0))
        self.assertEqual(rec["w2_src_max"], 11)
        self.assertEqual(rec["w1_est_max"], 2)
        self.assertAlmostEqual(rec["dag_ratio_est_max"], 33 / 8)
        self.assertEqual((rec["ratio"], rec["both"]), (2.0, 0))
        self.assertEqual(rec["trivial_frac"], 1.0)
        self.assertAlmostEqual(rec["removable_w2_est_at_8"], 1 - 9 / 33)
        # three `by simp` goals -> the whole automation-axis profile.
        self.assertEqual(rec["method_kinds"],
                         {"automation": 3, "search": 0, "arith": 0,
                          "structural": 0, "other": 0})


class ProofSize(unittest.TestCase):
    """Length axis (size): proof-body line/token counts, raw vs code."""

    def test_lines_and_tokens_raw_and_code(self):
        # The proof body is lines 4..8 (`proof -` .. `qed`); the theory-closing
        # `end` is a span-bounding command, not part of the proof, so it is no
        # longer miscounted as a body line.  The two-line `\<comment>` at (5, 6)
        # is the only prose, so `code` drops those 2 lines and their 8 tokens.
        snip = r'''theory T imports Main begin

lemma foo: "P \<longrightarrow> P"
proof -
  \<comment> \<open>this is a
  two-line comment\<close>
  show "P \<longrightarrow> P" by simp
qed

end
'''
        sec = section_from(snip)
        e = sec.entries[0]
        self.assertEqual((e.proof_line, e.body_end_line), (4, 8))
        self.assertEqual(shape._noise_spans(sec), [(5, 6)])
        rec = shape.summary_record(shape.summarize(shape.analyze_proof(sec, e)))
        self.assertEqual(rec["proof_lines"], 5)         # 8 - 4 + 1
        self.assertEqual(rec["proof_lines_code"], 3)    # minus the 2 comment lines
        self.assertEqual(rec["proof_tokens"], 19)
        self.assertEqual(rec["proof_tokens_code"], 11)  # minus 8 comment tokens
        self.assertEqual(rec["entry_lines"], e.line_count)
        # prose is derivable (raw - code), never stored as its own column.
        self.assertNotIn("proof_lines_prose", rec)

    def test_region_counts_empty_span_is_zero(self):
        sec = section_from('theory T imports Main begin\n'
                           'lemma a: "P" by simp\nend\n')
        self.assertEqual(shape._region_counts(sec, 0, 0), (0, 0, 0, 0))
        self.assertEqual(shape._region_counts(sec, 5, 2), (0, 0, 0, 0))  # hi < lo


if __name__ == "__main__":
    unittest.main()
