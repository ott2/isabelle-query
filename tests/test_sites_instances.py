r"""`instances`: where a locale or class is instantiated [instantiation-sites].

The verb lists the lines that SUPPLY types or terms to a locale or class —
`instantiation` / `instance` arities, `interpretation` /
`global_interpretation` / `interpret`, and `sublocale` — read where a command
can start, on the live view, so a heading, a comment, a `text` block or a
`\<^cancel>` that spells the command word is not a site.  Extending a target
(`class X = L + ...`, `sublocale L \<subseteq> M`'s `L` side) is a different
relation and not a site; it is the edge `-r` walks (`TheHierarchy` below).

Every expectation below was read off the fixture theories by hand before the
scan ran, and the line numbers are part of the expectation: do not insert
lines without moving them.  Each fixture theory pins one thing —
`Sites_Fix` the command set and the decoys, `Names_Fix` the NAME column's
fallback chain (written qualifier, sublocale target, enclosing block or
entry, honest `?`), `Closure_Fix` the class hierarchy.

Real files with a ROOT, because the import-visibility filter reads `imports`
clauses off disk.
"""

import io
import os
import sys
import tempfile
import unittest
import unittest.mock
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli, commands, sites  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402
from support import blank_terms  # noqa: E402

SITES_FIX = r'''theory Sites_Fix
  imports Main
begin

section \<open>A heading that says interpretation magma is not a command\<close>

locale magma =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale semi = magma +
  assumes assoc: "f (f x y) z = f x (f y z)"

locale magma\<^sub>2 =
  fixes h :: "'a \<Rightarrow> 'a"

locale "open" =
  fixes g :: "'a \<Rightarrow> 'a"

class mynull =
  fixes null :: 'a

interpretation nat_magma: magma "(+)" ..

global_interpretation int_magma: magma "(*)" ..

sublocale semi \<subseteq> magma f ..

sublocale magma < dual: magma "\<lambda>x y. f y x" ..

interpretation m2: magma\<^sub>2 id ..

interpretation q: "open" id ..

lemma uses_interpret: "True"
proof -
  interpret loc: magma "(+)" ..
  show ?thesis by simp
qed

instantiation nat :: mynull
begin
definition null_nat :: nat where "null_nat = (0::nat)"
instance ..
end

instantiation bool :: "{mynull, ord}"
begin
definition null_bool :: bool where "null_bool = False"
instance ..
end

instance prod :: (mynull, mynull) mynull ..

text \<open>
  interpretation magma "(-)" ..
\<close>

lemma decoy: "True"
  (* interpretation magma "(-)" .. *)
  by simp

\<^cancel>\<open>interpretation magma "(div)" ..\<close>

end
'''

NAMES_FIX = r'''theory Names_Fix
  imports Main
begin

locale plain =
  fixes p :: "'a \<Rightarrow> 'a"

locale holder =
  fixes q :: "'a \<Rightarrow> 'a"
begin

interpretation plain q ..

sublocale sub: plain q ..

end

interpretation plain id ..

sublocale holder \<subseteq> inner: plain q ..

lemma anon_interpret: "True"
proof -
  interpret plain id ..
  show ?thesis by simp
qed

end
'''

CLOSURE_FIX = r'''theory Closure_Fix
  imports Main
begin

class hasb =
  fixes b :: 'a

class base = hasb +
  assumes base_refl: "b = b"

class mid = base +
  assumes mid_refl: "b = b"

class leaf = mid +
  assumes leaf_refl: "b = b"

class side = hasb +
  assumes side_refl: "b = b"

class both = side + leaf

class qmid = Closure_Fix.base +
  assumes qmid_refl: "b = b"

class alt = hasb +
  assumes alt_refl: "b = b"
begin
subclass base
  by standard simp
end

instantiation nat :: leaf
begin
definition b_nat :: nat where "b_nat = 0"
instance by standard simp
end

instantiation int :: base
begin
definition b_int :: int where "b_int = 0"
instance by standard simp
end

instantiation bool :: side
begin
definition b_bool :: bool where "b_bool = False"
instance by standard simp
end

instantiation prod :: (hasb, hasb) hasb
begin
definition b_prod :: "'a \<times> 'b" where "b_prod = (b, b)"
instance ..
end

instance prod :: (both, both) both
  by standard simp

instantiation "fun" :: (type, mid) mid
begin
definition b_fun :: "'a \<Rightarrow> 'b" where "b_fun = (\<lambda>_. b)"
instance by standard simp
end

instantiation unit :: qmid
begin
definition b_unit :: unit where "b_unit = ()"
instance by standard simp
end

instantiation option :: (alt) alt
begin
definition b_option :: "'a option" where "b_option = Some b"
instance by standard simp
end

text \<open>
  class ghost = base +
    fixes g :: 'a
\<close>

(* class ghost2 = base + fixes g :: 'a *)

\<^cancel>\<open>instantiation char :: base begin instance .. end\<close>

end
'''

ROOT = ("session Fix = HOL +\n  theories\n    Sites_Fix\n    Names_Fix\n"
        "    Closure_Fix\n")


def heads(text):
    return sites.expression_heads(text, blank_terms(text))


def instances(text):
    return sites.expression_instances(text, blank_terms(text))


def arity(text):
    return sites.arity_classes(text, blank_terms(text))


def parts(text):
    return sites.arity_parts(text, blank_terms(text))


class TheGrammars(unittest.TestCase):
    """The parsers, pinned on strings: live text in, outer text simulated."""

    def test_expression_heads(self):
        for text, want in [
            (" magma f", ["magma"]),
            (" add: comm_monoid plus 0", ["comm_monoid"]),
            (" weak?: weak_complete_lattice", ["weak_complete_lattice"]),
            (' "and": semilattice_neutr \\<open>(AND)\\<close>',
             ["semilattice_neutr"]),
            (' q: "open" id', ["open"]),
            (" m2: magma\\<^sub>2 id", ["magma\\<^sub>2"]),
            (" Groups.monoid plus", ["Groups.monoid"]),
            (" L1 x + qual: L2 y", ["L1", "L2"]),
            (' folding "\\<lambda>x. x + 1" 0', ["folding"]),
        ]:
            with self.subTest(text=text):
                self.assertEqual(heads(text), want)

    def test_expression_instances(self):
        for text, want in [
            (' nat_magma: magma "(+)" ', [("nat_magma", "magma")]),
            (' "and": semilattice_neutr x', [("and", "semilattice_neutr")]),
            (" weak?: weak_complete_lattice x",
             [("weak", "weak_complete_lattice")]),
            (" magma f", [("", "magma")]),
            (" L1 x + q: L2 y", [("", "L1"), ("q", "L2")]),
        ]:
            with self.subTest(text=text):
                self.assertEqual(instances(text), want)

    def test_arity_classes(self):
        for text, want in [
            (" nat :: mynull", ["mynull"]),
            # Argument sorts are CONSTRAINTS, not instantiations.
            (" prod :: (exhaustive, exhaustive) exhaustive", ["exhaustive"]),
            (' bool :: "{order_bot, order_top, linorder}" ',
             ["order_bot", "order_top", "linorder"]),
            (' "fun" :: (type, ord) ord', ["ord"]),
            (' "fun" :: ("{equal,exhaustive}", exhaustive) exhaustive',
             ["exhaustive"]),
            # A class inclusion and a bare `instance ..` have no `::`.
            (" bifinite \\<subseteq> profinite", []),
            (" ..", []),
        ]:
            with self.subTest(text=text):
                self.assertEqual(arity(text), want)

    def test_arity_parts(self):
        for text, want in [
            (" prod :: (topological_space, topological_space) "
             "topological_space",
             ("prod", "(topological_space, topological_space) "
                      "topological_space")),
            (' "fun" :: (type, ord) ord', ("fun", "(type, ord) ord")),
            # Verbatim: a quoted brace sort stays quoted.
            (' bool :: "{mynull, ord}" ', ("bool", '"{mynull, ord}"')),
        ]:
            with self.subTest(text=text):
                self.assertEqual(parts(text), want)

    def test_denotes(self):
        self.assertTrue(sites.denotes("monoid", "monoid"))
        self.assertTrue(sites.denotes("Groups.monoid", "monoid"))
        self.assertFalse(sites.denotes("foo_monoid", "monoid"))


class SitesFixture(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        for name, text in (("Sites_Fix", SITES_FIX), ("Names_Fix", NAMES_FIX),
                           ("Closure_Fix", CLOSURE_FIX)):
            (self.dir / f"{name}.thy").write_text(text, encoding="utf-8")
        (self.dir / "ROOT").write_text(ROOT, encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def inst(self, name):
        return sites.find_instantiations(self.sections, name)

    @staticmethod
    def loci(found):
        return [f"{s.theory}:{s.line}" for s in found]

    def run_cmd(self, fn, *args):
        out = io.StringIO()
        with redirect_stdout(out):
            fn(*args)
        return out.getvalue()

    def unresolved(self, fn, *args):
        """Run `fn`, expecting exit 1, a diagnostic on stderr and NOTHING on
        stdout — so `$(...)` captures nothing and `$?` says why."""
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            with self.assertRaises(SystemExit) as caught:
                fn(*args)
        self.assertEqual(caught.exception.code, 1)
        self.assertEqual(out.getvalue(), "")
        return err.getvalue()


class TheEngineOnTheFixture(SitesFixture):

    def test_the_fixture_loaded_whole(self):
        self.assertEqual([s.theory for s in self.sections],
                         ["Sites_Fix", "Names_Fix", "Closure_Fix"])

    def test_magma(self):
        found = self.inst("magma")
        self.assertEqual(self.loci(found),
                         ["Sites_Fix:22", "Sites_Fix:24", "Sites_Fix:26",
                          "Sites_Fix:28", "Sites_Fix:36"])
        self.assertEqual([s.kind for s in found],
                         ["interpretation", "global_interpretation",
                          "sublocale", "sublocale", "interpret"])
        self.assertEqual([s.name for s in found],
                         ["nat_magma", "int_magma", "semi", "dual", "loc"])
        # Nothing at or past the `text` block (55), the comment (59) or the
        # `\<^cancel>` (62): those are not live command positions.
        self.assertTrue(all(s.line < 55 for s in found))

    def test_extending_is_not_instantiating(self):
        # `locale semi = magma + ...` (line 10) supplies nothing to magma.
        self.assertNotIn(10, [s.line for s in self.inst("magma")])

    def test_a_sublocale_is_a_site_of_its_target_only(self):
        # `sublocale semi \<subseteq> magma f ..` is a site of magma (26),
        # never of semi.
        self.assertEqual(self.inst("semi"), [])

    def test_a_symbol_bearing_and_a_quoted_locale_name(self):
        self.assertEqual(self.loci(self.inst("magma\\<^sub>2")),
                         ["Sites_Fix:30"])
        self.assertEqual(self.loci(self.inst("open")), ["Sites_Fix:32"])

    def test_mynull(self):
        found = self.inst("mynull")
        self.assertEqual(self.loci(found),
                         ["Sites_Fix:40", "Sites_Fix:46", "Sites_Fix:52"])
        self.assertEqual([s.kind for s in found],
                         ["instantiation", "instantiation", "instance"])
        self.assertEqual([s.name for s in found], ["nat", "bool", "prod"])
        # The bare `instance ..` closing each block (43, 49) is not a second
        # site.
        self.assertEqual([s.label(True) for s in found],
                         ["nat :: mynull", 'bool :: "{mynull, ord}"',
                          "prod :: (mynull, mynull) mynull"])
        self.assertEqual([s.label(False) for s in found],
                         ["nat", "bool", "prod"])

    def test_the_name_column_fallback_chain(self):
        found = self.inst("plain")
        self.assertEqual(self.loci(found),
                         ["Names_Fix:12", "Names_Fix:14", "Names_Fix:18",
                          "Names_Fix:20", "Names_Fix:24"])
        # The enclosing block, the written qualifier, the honest `?`, the
        # qualifier over the sublocale target, the enclosing entry.
        self.assertEqual([s.name for s in found],
                         ["holder", "sub", "?", "inner", "anon_interpret"])
        # An interpretation writes no sort.
        self.assertEqual([s.label(True) for s in found],
                         [s.label(False) for s in found])

    def test_a_bare_interpretation_is_not_named_after_the_locale(self):
        by_line = {s.line: s for s in self.inst("plain")}
        self.assertEqual(by_line[18].name, "?")
        self.assertEqual(by_line[20].name, "inner")

    def test_the_hierarchy_theory_direct_sites(self):
        self.assertEqual(self.loci(self.inst("base")), ["Closure_Fix:38"])
        self.assertEqual(self.loci(self.inst("side")), ["Closure_Fix:44"])

    def test_the_source_cell_is_the_raw_line(self):
        by_line = {s.line: s for s in self.inst("magma")}
        self.assertEqual(by_line[22].text,
                         'interpretation nat_magma: magma "(+)" ..')


class SubjectResolution(SitesFixture):

    def resolve(self, name, tags=sites.LOCALE_TAGS, what="a locale or class"):
        return commands._resolve_site_subject(self.sections, name, tags, what)

    def test_a_locale_and_a_class_resolve(self):
        self.assertEqual(self.resolve("magma").tag, "LOCALE")
        self.assertEqual(self.resolve("mynull").tag, "CLASS")
        self.assertEqual(self.resolve("magma").how, "")

    def test_an_unknown_name_is_a_reason(self):
        self.assertEqual(
            self.resolve("no_such_thing"),
            "'no_such_thing' is not a locale or class declared in this "
            "project")

    def test_a_wrong_kinded_name_names_its_kind_and_theory(self):
        self.assertEqual(
            self.resolve("uses_interpret"),
            "'uses_interpret' is a LEMMA in Sites_Fix, not a locale or class")


class TheCommand(SitesFixture):

    def instances(self, name, **kw):
        return self.run_cmd(commands.cmd_instances, self.sections, name,
                            CmdFlags(**kw))

    def test_counts(self):
        for name, want in (("semi", "0\n"), ("magma", "5\n"),
                           ("mynull", "3\n"), ("base", "1\n")):
            with self.subTest(name=name):
                self.assertEqual(self.instances(name, mode="count"), want)

    def test_names_are_bare_loci(self):
        self.assertEqual(self.instances("mynull", mode="names"),
                         "Sites_Fix:40\nSites_Fix:46\nSites_Fix:52\n")
        # Nothing at all for a known subject with no sites.
        self.assertEqual(self.instances("semi", mode="names"), "")

    def test_the_table_byte_for_byte(self):
        self.assertEqual(
            self.instances("base"),
            "1 instantiation(s) of base:\n"
            "\n"
            "  Closure_Fix:38  int  instantiation  instantiation int :: base\n")

    def test_the_padded_columns(self):
        # Locus 12, name 9 (`nat_magma`), kind 21 (`global_interpretation`),
        # each followed by two spaces; the source cell is stripped and never
        # padded.
        got = self.instances("magma").splitlines()
        self.assertEqual(got[0], "5 instantiation(s) of magma:")
        self.assertEqual(got[1], "")
        self.assertEqual(
            got[2],
            "  Sites_Fix:22  nat_magma  interpretation         "
            'interpretation nat_magma: magma "(+)" ..')
        self.assertEqual(
            got[4],
            "  Sites_Fix:26  semi       sublocale              "
            "sublocale semi \\<subseteq> magma f ..")
        self.assertFalse(any(line.endswith(" ") for line in got))

    def test_an_honest_zero(self):
        self.assertEqual(self.instances("semi"),
                         "No instantiations found for 'semi'.\n")

    def test_the_name_column_end_to_end(self):
        names = [line.split()[1] for line in
                 self.instances("plain").splitlines()[2:]]
        self.assertEqual(names, ["holder", "sub", "?", "inner",
                                 "anon_interpret"])

    def test_sorts_is_written_text(self):
        on = self.instances("mynull", sorts=True)
        for cell in ("nat :: mynull", 'bool :: "{mynull, ord}"',
                     "prod :: (mynull, mynull) mynull"):
            self.assertIn(f"  {cell}  ", on)
        off = [line.split()[1] for line in
               self.instances("mynull").splitlines()[2:]]
        self.assertEqual(off, ["nat", "bool", "prod"])

    def test_an_unknown_subject_is_a_refusal(self):
        err = self.unresolved(commands.cmd_instances, self.sections,
                              "no_such_locale_xyz", CmdFlags())
        self.assertIn("'no_such_locale_xyz' is not a locale or class "
                      "declared in this project", err)
        self.assertNotIn("ERROR:", err)

    def test_a_wrong_kinded_subject_is_a_refusal(self):
        err = self.unresolved(commands.cmd_instances, self.sections,
                              "uses_interpret", CmdFlags())
        self.assertIn("'uses_interpret' is a LEMMA in Sites_Fix, not a "
                      "locale or class", err)

    def test_count_mode_on_an_unresolved_subject_prints_nothing(self):
        # Never a plausible `0`: the refusal happens before the mode switch.
        self.unresolved(commands.cmd_instances, self.sections,
                        "no_such_locale_xyz", CmdFlags(mode="count"))


class TheParser(unittest.TestCase):

    def parse(self, *argv):
        return cli._build_parser().parse_args(list(argv))

    def test_the_flags(self):
        ns = self.parse("instances", "L", "-c", "--names", "--sorts")
        self.assertTrue(ns.count and ns.names and ns.sorts)
        self.assertFalse(ns.recursive)
        self.assertEqual(ns.name, ["L"])

    def test_count_beats_names(self):
        f = cli._flags_from_ns(self.parse("instances", "L", "--names", "-c"))
        self.assertEqual(f.mode, "count")
        self.assertFalse(f.sorts)
        self.assertTrue(cli._flags_from_ns(
            self.parse("instances", "L", "--sorts")).sorts)

    def test_no_reach_flag(self):
        # The import-visibility filter is unconditional here: an
        # `interpretation L` in a theory that cannot see L interprets a
        # different L, and there is no name-only answer worth offering.
        err = io.StringIO()
        with redirect_stderr(err), self.assertRaises(SystemExit) as caught:
            self.parse("instances", "L", "--reach", "name")
        self.assertEqual(caught.exception.code, 2)
        self.assertIn("--reach", err.getvalue())

    def test_at_least_one_subject(self):
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.parse("instances")

    def test_recursive(self):
        self.assertTrue(self.parse("instances", "L", "-r").recursive)
        self.assertTrue(cli._flags_from_ns(
            self.parse("instances", "L", "-rc")).recursive)


def ext(text):
    return sites.extends_heads(text, blank_terms(text))


class TheHierarchy(SitesFixture):
    r"""`-r`: the extension relation, hand-computed off `Closure_Fix` (an
    arrow reads "extends")::

        base -> hasb  (8)          mid -> base   (11)
        leaf -> mid   (14)         side -> hasb  (17)
        both -> side, leaf  (20)   qmid -> base  (22, QUALIFIED)
        alt -> hasb   (25), alt -> base  (28, a `subclass` inside alt's block)

    so descendants(base) = {mid, qmid, alt, leaf, both}, and the transitive
    sites of `base` are the six arities of those classes plus its own --
    every one in the file except `bool :: side` (44), whose class is a
    SIBLING, except `prod :: (hasb, hasb) hasb` (50), whose class is base's
    PARENT, and except the three decoys (78, 82, 84) that are not live text.
    """

    def test_extends_heads(self):
        for text, want in [
            ("class X = A + B + fixes f :: 'a", ["A", "B"]),
            ('class X = A + assumes eq: "a = b" ', ["A"]),
            ("class X = A + constrains f :: 'a", ["A"]),
            ("class X = A + notes foo = bar", ["A"]),
            ("class X = A", ["A"]),
            ("class X = fixes f :: 'a", []),
            ('locale X = q: "open" id + Groups.monoid plus',
             ["open", "Groups.monoid"]),
            ('locale X = folding "\\<lambda>x. x + 1" 0', ["folding"]),
        ]:
            with self.subTest(text=text):
                self.assertEqual(ext(text), want)

    def extenders(self, name):
        return sorted(sites.extenders(self.sections, name))

    def descendants(self, name):
        return sorted(sites.descendants(self.sections, name))

    def test_extenders(self):
        self.assertEqual(self.extenders("hasb"), ["alt", "base", "side"])
        self.assertEqual(self.extenders("base"), ["alt", "mid", "qmid"])
        self.assertEqual(self.extenders("mid"), ["leaf"])
        self.assertEqual(self.extenders("leaf"), ["both"])
        self.assertEqual(self.extenders("side"), ["both"])
        self.assertEqual(self.extenders("both"), [])

    def test_decoys_are_not_extenders(self):
        # `class ghost = base +` in a `text` block, `ghost2` in a comment.
        self.assertNotIn("ghost", self.extenders("base"))
        self.assertNotIn("ghost2", self.extenders("base"))

    def test_descendants(self):
        self.assertEqual(self.descendants("base"),
                         ["alt", "both", "leaf", "mid", "qmid"])
        self.assertEqual(self.descendants("mid"), ["both", "leaf"])
        self.assertEqual(self.descendants("side"), ["both"])
        self.assertEqual(self.descendants("both"), [])
        # A class never has its own parent among its descendants.
        self.assertNotIn("hasb", self.descendants("base"))

    def test_a_locale_is_not_its_own_descendant(self):
        # `semi` extends magma twice over (its header, and the `sublocale`
        # at Sites_Fix:26); `sublocale magma < dual: magma ...` is a
        # self-edge that neither loops nor makes magma its own descendant.
        self.assertEqual(self.descendants("magma"), ["semi"])

    def trans(self, name):
        return sites.find_instantiations_transitive(self.sections, name)

    def test_the_transitive_sites_of_base(self):
        rows = self.trans("base")
        self.assertEqual(self.loci([s for s, _v in rows]),
                         ["Closure_Fix:32", "Closure_Fix:38", "Closure_Fix:56",
                          "Closure_Fix:59", "Closure_Fix:65",
                          "Closure_Fix:71"])
        self.assertEqual([v for _s, v in rows],
                         ["leaf", "base", "both", "mid", "qmid", "alt"])
        self.assertEqual([s.kind for s, _v in rows],
                         ["instantiation", "instantiation", "instance",
                          "instantiation", "instantiation", "instantiation"])
        self.assertEqual([s.name for s, _v in rows],
                         ["nat", "int", "prod", "fun", "unit", "option"])
        # The sibling (44) and the parent's own arity (50) are not among
        # them.
        self.assertNotIn(44, [s.line for s, _v in rows])
        self.assertNotIn(50, [s.line for s, _v in rows])

    def test_the_transitive_sites_of_the_rest(self):
        for name, want in [
            ("mid", ["Closure_Fix:32", "Closure_Fix:56", "Closure_Fix:59"]),
            ("side", ["Closure_Fix:44", "Closure_Fix:56"]),
            ("both", ["Closure_Fix:56"]),
            ("hasb", ["Closure_Fix:32", "Closure_Fix:38", "Closure_Fix:44",
                      "Closure_Fix:50", "Closure_Fix:56", "Closure_Fix:59",
                      "Closure_Fix:65", "Closure_Fix:71"]),
        ]:
            with self.subTest(name=name):
                self.assertEqual(self.loci([s for s, _v in self.trans(name)]),
                                 want)

    def test_a_leaf_of_the_hierarchy_is_its_direct_listing(self):
        for name in ("both", "qmid", "alt"):
            with self.subTest(name=name):
                self.assertEqual(self.loci([s for s, _v in self.trans(name)]),
                                 self.loci(self.inst(name)))

    def test_no_dedup_pass_is_needed(self):
        # `sublocale semi \<subseteq> magma f ..` (26) is both a site of
        # magma and the edge that brings semi's (nonexistent) sites in: it
        # appears exactly once, and every row is via magma itself.
        rows = self.trans("magma")
        self.assertEqual(self.loci([s for s, _v in rows]),
                         self.loci(self.inst("magma")))
        self.assertEqual([s.line for s, _v in rows].count(26), 1)
        self.assertEqual({v for _s, v in rows}, {"magma"})
        self.assertEqual(self.trans("semi"), [])


class TheClosureIsBuiltOnce(SitesFixture):
    """The cost of `-r` scales with the corpus, not with the hierarchy.

    Over the distribution's `src/HOL`, `instances ab_semigroup_add -r` walks a
    hierarchy of some 430 classes.  A fresh visibility per name re-indexed
    every entry and re-read every theory header once per name, and the
    single-slot closure cache thrashed as the edge walk alternated theories:
    90 s against 6 s for the direct form.  One shared visibility per request,
    with closures memoised per theory, is the fix, and these counts are what
    pin it.
    """

    def test_each_header_is_read_at_most_once(self):
        from isabelle_query import graph
        calls = []
        real = graph.parse_thy_imports

        def counting(path):
            calls.append(path)
            return real(path)

        with unittest.mock.patch.object(graph, "parse_thy_imports", counting):
            rows = sites.find_instantiations_transitive(self.sections, "base")
        self.assertEqual(len(rows), 6)
        self.assertLessEqual(len(calls), len(self.sections))

    def test_one_visibility_per_request(self):
        from isabelle_query import graph
        built = []
        real_init = graph._Visibility.__init__

        def counting(self_, *args, **kwargs):
            built.append(kwargs)
            real_init(self_, *args, **kwargs)

        with unittest.mock.patch.object(graph._Visibility, "__init__",
                                        counting):
            rows = sites.find_instantiations_transitive(self.sections, "hasb")
        self.assertEqual(len(rows), 8)
        self.assertEqual(len(built), 1)
        self.assertTrue(built[0].get("bound_names"))

    def test_a_name_declared_nowhere_builds_no_closure(self):
        from isabelle_query import graph
        vis = graph._Visibility(self.sections, bound_names=True,
                                memo_closures=True)
        admits = graph.site_filter(self.sections, "nothing_declares_this",
                                   vis=vis)
        self.assertTrue(admits("Closure_Fix"))
        self.assertEqual(vis._closures, {})


class TheTransitiveCommand(SitesFixture):

    def instances(self, name, **kw):
        return self.run_cmd(commands.cmd_instances, self.sections, name,
                            CmdFlags(recursive=True, **kw))

    def test_counts(self):
        for name, want in (("base", "6\n"), ("mid", "3\n"), ("side", "2\n"),
                           ("both", "1\n"), ("magma", "5\n"), ("hasb", "8\n")):
            with self.subTest(name=name):
                self.assertEqual(self.instances(name, mode="count"), want)

    def test_the_default_form_is_untouched(self):
        self.assertEqual(self.run_cmd(commands.cmd_instances, self.sections,
                                      "base", CmdFlags(mode="count")), "1\n")

    def test_names(self):
        self.assertEqual(
            self.instances("base", mode="names"),
            "Closure_Fix:32\nClosure_Fix:38\nClosure_Fix:56\nClosure_Fix:59\n"
            "Closure_Fix:65\nClosure_Fix:71\n")

    def test_the_table_with_its_via_column(self):
        # Locus 14, name 6 (`option`), kind 13 (`instantiation`), VIA 4
        # (`leaf` / `both` / `qmid`), each followed by two spaces.  Line 56
        # wraps its proof onto the next line, so its source cell ends at
        # `both`.
        self.assertEqual(
            self.instances("base"),
            "6 instantiation(s) of base (transitive):\n"
            "\n"
            "  Closure_Fix:32  nat     instantiation  leaf  "
            "instantiation nat :: leaf\n"
            "  Closure_Fix:38  int     instantiation  base  "
            "instantiation int :: base\n"
            "  Closure_Fix:56  prod    instance       both  "
            "instance prod :: (both, both) both\n"
            "  Closure_Fix:59  fun     instantiation  mid   "
            'instantiation "fun" :: (type, mid) mid\n'
            "  Closure_Fix:65  unit    instantiation  qmid  "
            "instantiation unit :: qmid\n"
            "  Closure_Fix:71  option  instantiation  alt   "
            "instantiation option :: (alt) alt\n")

    def test_sorts_is_orthogonal(self):
        got = self.instances("base", sorts=True)
        self.assertIn("  nat :: leaf  ", got)
        loci = [line.split()[0] for line in got.splitlines()[2:]]
        self.assertEqual(loci, ["Closure_Fix:32", "Closure_Fix:38",
                                "Closure_Fix:56", "Closure_Fix:59",
                                "Closure_Fix:65", "Closure_Fix:71"])

    def test_the_exit_contract_is_the_same_question(self):
        self.assertEqual(self.instances("semi"),
                         "No instantiations found for 'semi'.\n")
        for name in ("no_such_locale_xyz", "uses_interpret"):
            with self.subTest(name=name):
                self.unresolved(commands.cmd_instances, self.sections, name,
                                CmdFlags(recursive=True))


if __name__ == "__main__":
    unittest.main()
