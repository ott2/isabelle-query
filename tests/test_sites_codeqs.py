r"""`codeqs`: the declared code-equation sites of a constant [code-equations].

Three producers, and the KIND column says which: the constant's own
`definition` / `fun` (`default` -- its equations are registered with no
attribute written), a declaration carrying a `code`-family attribute whose
statement's left-hand-side HEAD is the constant (`[code]`, `[code del]`, ...),
and a `declare` / `lemmas` that attaches one to a named fact of the constant,
or a `[[code drop:]]` naming it outright.  `code_unfold` and kin are a
different store (the preprocessor) and are not sites.  A constant on a
right-hand side is not a site; a `(* ... *)` note or a `\<^cancel>` is not.

Every expectation below was read off the fixture theories by hand before the
scan ran; the line numbers are part of the expectation.  `Nested_Fix` and
`Deeper_Fix` sit in subdirectory sessions so that `quad` is registered in one
directory and RETRACTED in another, the case a per-theory listing has to
place.  `Examples` twice over, in `alpha/` and `beta/`, is the collision
fixture for both verbs: a locus must name ONE theory, or `--names` does not
round-trip through `enclosing`.
"""

import io
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli, commands, sites  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402
from test_sites_instances import blank_terms  # noqa: E402

CODE_FIX = r'''theory Code_Fix
  imports Main
begin

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

definition twice :: "nat \<Rightarrow> nat" where
  "twice n = n + n"

definition thrice :: "nat \<Rightarrow> nat" where [code]: "thrice n = n + n + n"

definition half :: "nat \<Rightarrow> nat" where
  "half n = n div 2"

definition x\<^sub>1 :: nat where
  "x\<^sub>1 = 1"

datatype mytree = Leaf | Node mytree mytree

lemma twice_alt [code]: "twice n = 2 * n"
  by (simp add: twice_def)

lemma not_a_code_eq [code_unfold]: "twice n = n + n"
  by (simp add: twice_def)

lemma mentions_only [code]: "thrice n = twice n + n"
  by (simp add: twice_def thrice_def)

lemma cond_code [code]: "n > 0 \<Longrightarrow> half n = n div 2"
  by (simp add: half_def)

lemma x1_code [code]: "x\<^sub>1 = 1"
  by (simp add: x\<^sub>1_def)

lemma node_code [code]: "Node l r = Node l r"
  by simp

declare fib.simps [code del]

lemmas twice_lemmas [code] = twice_alt

declare [[code drop: twice]]

lemma decoy_code: "True"
  (* declare twice_def [code] *)
  by simp

\<^cancel>\<open>lemma cancelled_code [code]: "twice n = 0"\<close>

end
'''

NESTED_FIX = r'''theory Nested_Fix
  imports Code_Fix
begin

definition quad :: "nat \<Rightarrow> nat" where
  "quad n = twice (twice n)"

lemma quad_code [code]: "quad n = 4 * n"
  by (simp add: quad_def twice_def)

end
'''

DEEPER_FIX = r'''theory Deeper_Fix
  imports Nested_Fix
begin

declare quad_code [code del]

end
'''

ROOT = '''session Fix = HOL +
  theories
    Code_Fix

session Fix_Nested in Nested = Fix +
  theories
    Nested_Fix

session Fix_Deep in "Deep/Down" = Fix_Nested +
  theories
    Deeper_Fix
'''


def attrs(text):
    return sites.code_attrs(text, blank_terms(text))


def wt(text, name):
    return sites.written_type(text, blank_terms(text), name)


class TheGrammars(unittest.TestCase):

    def test_code_attrs(self):
        for text, want in [
            ("lemma foo [code]: ", ["code"]),
            ("lemma foo [code equation]: ", ["code equation"]),
            ("lemma foo [code prepend]: ", ["code prepend"]),
            ("lemma foo [code nbe]: ", ["code nbe"]),
            ("lemma foo [code abstract]: ", ["code abstract"]),
            ("lemma foo [code abstype]: ", ["code abstype"]),
            ("declare f.simps [code del]", ["code del"]),
            ("declare [[code drop: f]]", ["code drop"]),
            ("declare [[code abort: f]]", ["code abort"]),
            # The preprocessor's attributes, and the predicate compiler's,
            # are a different store: the token boundary keeps them out.
            ("lemma foo [code_unfold]: ", []),
            ("lemma foo [code_abbrev]: ", []),
            ("lemma foo [code_post]: ", []),
            ("declare i [code_pred_intro]", []),
            ("lemma foo [simp, code, code_unfold]: ", ["code"]),
            # A `[` inside a term opens nothing.
            ('lemma foo: "f [x] = y"', []),
        ]:
            with self.subTest(text=text):
                self.assertEqual([a.spelling for a in attrs(text)], want)

    def test_the_config_form(self):
        got = attrs("declare [[code drop: f]]")
        self.assertEqual([(a.spelling, a.config) for a in got],
                         [("code drop", True)])
        self.assertEqual([a.config for a in attrs("declare f [code del]")],
                         [False])

    def test_dropped_constants(self):
        text = 'declare [[code drop: "open :: real set \\<Rightarrow> bool" g]]'
        (a,) = attrs(text)
        self.assertEqual(sites.dropped_constants(text, a), ["open", "g"])

    def test_equation_heads(self):
        for text, want in [
            (' "twice n = 2 * n" ', ["twice"]),
            (' "thrice n = twice n + n" ', ["thrice"]),
            (' "n > 0 \\<Longrightarrow> half n = n div 2" ', ["half"]),
            # The head after each `(` too, which is what makes an abstract
            # equation `Rep_T (f x) = ...` a site of `f`.
            (' "rep_pos (mk n) = max 1 n" ', ["rep_pos", "mk"]),
            (' "f x \\<equiv> g x" ', ["f"]),
            (' "p x \\<longleftrightarrow> q x" ', ["p"]),
            (' \\<open>f x = y\\<close> ', ["f"]),
            (' "f 0 = a" "g n = b" ', ["f", "g"]),
            (' assumes "p x = y" shows "f x = z" ', ["f"]),
            (' "x\\<^sub>1 = 1" ', ["x\\<^sub>1"]),
        ]:
            with self.subTest(text=text):
                self.assertEqual(sites.equation_heads(text), want)

    def test_written_type(self):
        for text, name, want in [
            ('definition twice :: "nat \\<Rightarrow> nat" where', "twice",
             "nat \\<Rightarrow> nat"),
            ("definition null_nat :: nat where", "null_nat", "nat"),
            # A `::` inside a term is not the declaration's own.
            ('lemma foo: "f :: nat \\<Rightarrow> bool" ', "f", ""),
            ('lemma twice_alt [code]: "twice n = 2 * n" ', "twice_alt", ""),
        ]:
            with self.subTest(text=text):
                self.assertEqual(wt(text, name), want)

    def test_cited_fact_names(self):
        outer = blank_terms("lemmas foo [code] = bar baz")
        self.assertEqual(sites.cited_fact_names(outer, 6),
                         ["foo", "bar", "baz"])
        outer = blank_terms("declare fib.simps [code del]")
        self.assertEqual(sites.cited_fact_names(outer, 7), ["fib.simps"])


class CodeFixture(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        (self.dir / "Nested").mkdir()
        (self.dir / "Deep" / "Down").mkdir(parents=True)
        (self.dir / "Code_Fix.thy").write_text(CODE_FIX, encoding="utf-8")
        (self.dir / "Nested" / "Nested_Fix.thy").write_text(
            NESTED_FIX, encoding="utf-8")
        (self.dir / "Deep" / "Down" / "Deeper_Fix.thy").write_text(
            DEEPER_FIX, encoding="utf-8")
        (self.dir / "ROOT").write_text(ROOT, encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def code(self, name):
        return sites.find_code_equations(self.sections, name)

    @staticmethod
    def loci(found):
        return [f"{s.theory}:{s.line}" for s in found]

    def run_cmd(self, fn, *args):
        out = io.StringIO()
        with redirect_stdout(out):
            fn(*args)
        return out.getvalue()

    def unresolved(self, fn, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            with self.assertRaises(SystemExit) as caught:
                fn(*args)
        self.assertEqual(caught.exception.code, 1)
        self.assertEqual(out.getvalue(), "")
        return err.getvalue()


class TheEngineOnTheFixture(CodeFixture):

    def test_the_fixture_loaded_whole(self):
        self.assertEqual([s.theory for s in self.sections],
                         ["Code_Fix", "Nested_Fix", "Deeper_Fix"])

    def test_twice(self):
        found = self.code("twice")
        self.assertEqual(self.loci(found),
                         ["Code_Fix:10", "Code_Fix:23", "Code_Fix:43",
                          "Code_Fix:45"])
        self.assertEqual([s.kind for s in found],
                         ["default", "[code]", "[code]", "[code drop]"])
        self.assertEqual([s.name for s in found],
                         ["twice", "twice_alt", "twice_lemmas", "twice"])
        # Only the definition writes a signature.
        self.assertEqual([s.label(True) for s in found],
                         ["twice :: nat \\<Rightarrow> nat", "twice_alt",
                          "twice_lemmas", "twice"])

    def test_a_right_hand_side_is_not_a_site(self):
        # `mentions_only [code]: "thrice n = twice n + n"` (29) is an
        # equation of thrice.
        self.assertNotIn(29, [s.line for s in self.code("twice")])
        self.assertIn(29, [s.line for s in self.code("thrice")])

    def test_the_preprocessor_attribute_is_not_a_site(self):
        self.assertNotIn(26, [s.line for s in self.code("twice")])

    def test_the_decoys_are_not_sites(self):
        lines = [s.line for s in self.code("twice")]
        self.assertNotIn(48, lines)   # `(* declare twice_def [code] *)`
        self.assertNotIn(51, lines)   # `\<^cancel>\<open>lemma ... [code]`

    def test_fib(self):
        found = self.code("fib")
        self.assertEqual(self.loci(found), ["Code_Fix:5", "Code_Fix:41"])
        self.assertEqual([s.kind for s in found], ["default", "[code del]"])
        self.assertEqual([s.name for s in found], ["fib", "fib.simps"])

    def test_a_declaration_with_an_attribute_has_no_default_row(self):
        found = self.code("thrice")
        self.assertEqual(self.loci(found), ["Code_Fix:13", "Code_Fix:29"])
        self.assertEqual([s.kind for s in found], ["[code]", "[code]"])

    def test_a_conditional_equation(self):
        found = self.code("half")
        self.assertEqual(self.loci(found), ["Code_Fix:15", "Code_Fix:32"])
        self.assertEqual([s.name for s in found], ["half", "cond_code"])

    def test_a_symbol_bearing_constant(self):
        self.assertEqual(self.loci(self.code("x\\<^sub>1")),
                         ["Code_Fix:18", "Code_Fix:35"])

    def test_a_constructor(self):
        self.assertEqual(self.loci(self.code("Node")), ["Code_Fix:38"])
        # A datatype registers constructors, not equations.
        self.assertEqual(self.code("Leaf"), [])

    def test_registered_here_and_retracted_there(self):
        found = self.code("quad")
        self.assertEqual(self.loci(found),
                         ["Nested_Fix:5", "Nested_Fix:8", "Deeper_Fix:5"])
        self.assertEqual([s.kind for s in found],
                         ["default", "[code]", "[code del]"])
        self.assertEqual([s.name for s in found],
                         ["quad", "quad_code", "quad_code"])


class SubjectResolution(CodeFixture):

    def resolve(self, name):
        return commands._resolve_site_subject(self.sections, name,
                                              sites.CONSTANT_TAGS,
                                              "a constant")

    def test_a_lemma_is_not_a_constant(self):
        got = self.resolve("twice_alt")
        self.assertIsInstance(got, str)
        self.assertIn("LEMMA", got)
        self.assertIn("Code_Fix", got)

    def test_a_constructor_resolves_through_its_binder(self):
        got = self.resolve("Leaf")
        self.assertEqual(got.how, "a constructor of mytree")
        self.assertEqual(got.name, "Leaf")
        self.assertEqual(got.tag, "DATATYPE")

    def test_a_primrec_is_a_constant(self):
        self.assertEqual(self.resolve("fib").tag, "FUN")


class TheCommand(CodeFixture):

    def codeqs(self, name, **kw):
        return self.run_cmd(commands.cmd_codeqs, self.sections, name,
                            CmdFlags(**kw))

    def test_counts(self):
        for name, want in (("twice", "4\n"), ("fib", "2\n"),
                           ("quad", "3\n"), ("Leaf", "0\n")):
            with self.subTest(name=name):
                got = self.codeqs(name, mode="count")
                self.assertTrue(got.endswith(want), got)

    def test_names(self):
        self.assertEqual(self.codeqs("quad", mode="names"),
                         "Nested_Fix:5\nNested_Fix:8\nDeeper_Fix:5\n")

    def test_the_table(self):
        self.assertEqual(
            self.codeqs("fib"),
            "2 code equation(s) of fib:\n"
            "\n"
            '  Code_Fix:5   fib        default     fun fib :: "nat '
            '\\<Rightarrow> nat" where\n'
            "  Code_Fix:41  fib.simps  [code del]  declare fib.simps "
            "[code del]\n")

    def test_sorts_only_where_a_signature_is_written(self):
        rows = self.codeqs("twice", sorts=True).splitlines()[2:]
        self.assertEqual(len(rows), 4)
        self.assertEqual(sum(1 for r in rows if " :: nat" in r), 1)
        self.assertIn("  twice :: nat \\<Rightarrow> nat  ", rows[0])

    def test_a_known_constant_with_no_equations(self):
        # The binding note first, in every mode, then the honest zero.
        self.assertEqual(self.codeqs("Leaf"),
                         "# 'Leaf' is a constructor of mytree.\n"
                         "No code equations found for 'Leaf'.\n")
        self.assertEqual(self.codeqs("Leaf", mode="count"),
                         "# 'Leaf' is a constructor of mytree.\n0\n")

    def test_a_lemma_is_a_refusal(self):
        err = self.unresolved(commands.cmd_codeqs, self.sections,
                              "twice_alt", CmdFlags())
        self.assertIn("'twice_alt' is a LEMMA in Code_Fix, not a constant",
                      err)
        self.assertNotIn("ERROR:", err)

    def test_an_unknown_constant_is_a_refusal_in_count_mode_too(self):
        err = self.unresolved(commands.cmd_codeqs, self.sections,
                              "no_such_const_xyz", CmdFlags(mode="count"))
        self.assertIn("'no_such_const_xyz' is not a constant declared in "
                      "this project", err)


class TheParser(unittest.TestCase):

    def parse(self, *argv):
        return cli._build_parser().parse_args(list(argv))

    def rejected(self, *argv):
        err = io.StringIO()
        with redirect_stderr(err), self.assertRaises(SystemExit) as caught:
            self.parse(*argv)
        self.assertEqual(caught.exception.code, 2)
        return err.getvalue()

    def test_the_flags(self):
        ns = self.parse("codeqs", "f", "g", "-c", "--names", "--sorts")
        self.assertTrue(ns.count and ns.names and ns.sorts)
        self.assertEqual(ns.name, ["f", "g"])
        self.assertEqual(cli._flags_from_ns(ns).mode, "count")

    def test_no_recursive_flag(self):
        self.assertIn("-r", self.rejected("codeqs", "f", "-r"))

    def test_no_reach_flag(self):
        self.assertIn("--reach", self.rejected("codeqs", "f", "--reach",
                                               "name"))


ALPHA = '''theory Examples
imports Main
begin

locale L =
  fixes g :: "'a \\<Rightarrow> 'a"

definition f :: "nat \\<Rightarrow> nat" where
  "f n = n + 1"

interpretation a_inst: L id ..

lemma a_eq [code]: "f n = Suc n"
  by (simp add: f_def)

end
'''

# Padded so that only line 8 coincides with alpha's.
BETA = '''theory Examples
imports Main
begin

locale L =
  fixes g :: "'a \\<Rightarrow> 'a"

definition f :: "nat \\<Rightarrow> nat" where
  "f n = n + 2"

lemma b_pad: "True" by simp

lemma b_pad2: "True" by simp

interpretation b_inst: L id ..

lemma b_eq [code]: "f n = Suc (Suc n)"
  by (simp add: f_def)

end
'''


class TheCollisionFixture(unittest.TestCase):
    """Two theories called `Examples`, in `alpha/` and `beta/`.

    Label derivation, by hand: at depth 1 both are `Examples` and neither
    settles; at depth 2 `alpha/Examples` and `beta/Examples` both do.  Neither
    verb may print the bare, ambiguous `Examples:N`.
    """

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        for sub, text in (("alpha", ALPHA), ("beta", BETA)):
            (self.dir / sub).mkdir()
            (self.dir / sub / "Examples.thy").write_text(text,
                                                        encoding="utf-8")
            (self.dir / sub / "ROOT").write_text(
                f"session {sub.title()} = HOL +\n  theories\n    Examples\n",
                encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def run_cmd(self, fn, name, **kw):
        out = io.StringIO()
        with redirect_stdout(out):
            fn(self.sections, name, CmdFlags(**kw))
        return out.getvalue()

    def test_sections_load_alpha_then_beta(self):
        self.assertEqual([s.theory for s in self.sections],
                         ["Examples", "Examples"])
        self.assertEqual([s.path.parent.name for s in self.sections],
                         ["alpha", "beta"])

    def test_names_are_qualified(self):
        self.assertEqual(self.run_cmd(commands.cmd_instances, "L",
                                      mode="names"),
                         "alpha/Examples:11\nbeta/Examples:15\n")
        self.assertEqual(self.run_cmd(commands.cmd_codeqs, "f", mode="names"),
                         "alpha/Examples:8\nalpha/Examples:13\n"
                         "beta/Examples:8\nbeta/Examples:17\n")

    def test_counts(self):
        self.assertEqual(self.run_cmd(commands.cmd_instances, "L",
                                      mode="count"), "2\n")
        self.assertEqual(self.run_cmd(commands.cmd_codeqs, "f",
                                      mode="count"), "4\n")

    def test_the_instances_table(self):
        self.assertEqual(
            self.run_cmd(commands.cmd_instances, "L"),
            "2 instantiation(s) of L:\n"
            "\n"
            "  alpha/Examples:11  a_inst  interpretation  "
            "interpretation a_inst: L id ..\n"
            "  beta/Examples:15   b_inst  interpretation  "
            "interpretation b_inst: L id ..\n")

    def test_the_codeqs_table(self):
        self.assertEqual(
            self.run_cmd(commands.cmd_codeqs, "f"),
            "4 code equation(s) of f:\n"
            "\n"
            "  alpha/Examples:8   f     default  "
            'definition f :: "nat \\<Rightarrow> nat" where\n'
            "  alpha/Examples:13  a_eq  [code]   "
            'lemma a_eq [code]: "f n = Suc n"\n'
            "  beta/Examples:8    f     default  "
            'definition f :: "nat \\<Rightarrow> nat" where\n'
            "  beta/Examples:17   b_eq  [code]   "
            'lemma b_eq [code]: "f n = Suc (Suc n)"\n')

    def test_no_row_prints_the_bare_name(self):
        for fn, name in ((commands.cmd_instances, "L"),
                         (commands.cmd_codeqs, "f")):
            for line in self.run_cmd(fn, name).splitlines()[2:]:
                self.assertNotRegex(line, r"^  Examples:\d")

    def test_sorts_leaves_the_locus_column_alone(self):
        got = self.run_cmd(commands.cmd_codeqs, "f", sorts=True)
        self.assertEqual([line.split()[0] for line in got.splitlines()[2:]],
                         ["alpha/Examples:8", "alpha/Examples:13",
                          "beta/Examples:8", "beta/Examples:17"])

    def test_every_locus_round_trips_through_enclosing(self):
        out = io.StringIO()
        with redirect_stdout(out):
            commands.cmd_enclosing(self.sections, ["alpha/Examples:13"])
        self.assertIn("a_eq (LEMMA)", out.getvalue())
        self.assertIn("alpha/Examples:13", out.getvalue())

    def test_an_unknown_subject_still_exits_1(self):
        err = io.StringIO()
        with redirect_stdout(io.StringIO()), redirect_stderr(err):
            with self.assertRaises(SystemExit) as caught:
                commands.cmd_instances(self.sections, "no_such_locale_xyz",
                                       CmdFlags())
        self.assertEqual(caught.exception.code, 1)


if __name__ == "__main__":
    unittest.main()
