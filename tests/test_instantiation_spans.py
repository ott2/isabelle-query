r"""Span-bounding outer commands, and deadness vs. fact identity.

Two defects, one root.  `compute_spans` ended an entry at the next
*entry-or-section* line, but several Isabelle outer commands declare nothing
and so are never indexed as entries — `instance`, `lemmas`, `declare`,
`code_printing`, `export_code`, and the `end` closing an enclosing block.
Each therefore fell INSIDE the span of the declaration above it.

The visible symptoms:

  (a) the span reported by `enclosing` / `outline` / `largest` / `show`
      overstated the declaration by the absorbed command;
  (b) a fact cited by the absorbed command sat inside that declaration's own
      def-site range, where the call-graph scan discards it as a self-mention
      — so the cited fact read as *unused*.

The canonical shape is an `equal` instantiation, where the definition's only
citation is the instance proof it swallows:

    instantiation foo :: equal begin
    definition "equal_foo (x::foo) y = (x = y)"
    instance by standard (simp add: equal_foo_def)
    end

Fixing spans alone is not enough: the freed line then belongs to no entry,
and `_build_call_graph` dropped entryless citations outright.  Both halves
are pinned below, along with the deliberate asymmetry that `foo_def` is a
distinct FACT from `foo` (so `callers` is unchanged — see
`test_substring_is_not_a_call`) while `unused` resolves it, because deleting
`definition foo` would break a proof citing `foo_def`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import cli, section_from, brute_force_call_graph  # noqa: E402


INSTANTIATION = r'''theory T imports Main begin

typedecl foo

instantiation foo :: equal begin
definition "equal_foo (x::foo) y = (x = y)"
instance by standard (simp add: equal_foo_def)
end

definition bar :: "nat" where "bar = 0"

end
'''


def _entry(sec, name):
    return next(e for e in sec.entries if e.name == name)


def _unused(*sections):
    graph = cli._build_call_graph(list(sections), derived=True)
    return set(cli._compute_unused(graph, set()))


class InstantiationSpans(unittest.TestCase):
    def test_definition_does_not_swallow_the_instance_proof(self):
        sec = section_from(INSTANTIATION, "T")
        eq = _entry(sec, "equal_foo")
        # The definition is one line; `instance` opens the next command.
        self.assertEqual(eq.thy_line, eq.thy_end)

    def test_instance_proof_keeps_its_definition_alive(self):
        sec = section_from(INSTANTIATION, "T")
        # `equal_foo` is cited only by the instance proof, and only as
        # `equal_foo_def` — both halves of the fix are needed to see it.
        self.assertNotIn("equal_foo", _unused(sec))

    def test_a_genuinely_uncited_definition_is_still_unused(self):
        sec = section_from(INSTANTIATION, "T")
        # The fix must not make everything look live: `bar` is cited nowhere.
        self.assertIn("bar", _unused(sec))


class TrailingCommandSpans(unittest.TestCase):
    def test_lemmas_alias_is_not_absorbed_by_the_lemma_above(self):
        sec = section_from(r'''theory T imports Main begin

definition baz :: "nat" where "baz = 0"

lemma quux: "baz = 0" by (simp add: baz_def)

lemmas quux_code [code] = quux

end
''', "T")
        q = _entry(sec, "quux")
        # The `lemmas` line is a command in its own right, not part of `quux`.
        self.assertLess(q.thy_end, 7)

    def test_boundary_does_not_land_on_a_separating_blank(self):
        sec = section_from(INSTANTIATION, "T")
        # `bar` is the last entry; the theory's closing `end` bounds it, but
        # the span must stop at bar's own last line, not the blank before it.
        bar = _entry(sec, "bar")
        self.assertEqual(bar.thy_line, bar.thy_end)

    def test_a_commented_out_command_is_not_a_boundary(self):
        sec = section_from(r'''theory T imports Main begin

definition wib :: "nat" where
  "wib = 0"
(* end *)

end
''', "T")
        # A commented-out `end` is prose; it must not cut the declaration.
        self.assertGreaterEqual(_entry(sec, "wib").thy_end, 4)


class DeadnessVersusFactIdentity(unittest.TestCase):
    """`foo_def` is a different fact from `foo`, but it is not a different
    DECLARATION — the two questions get different answers on purpose."""

    THY = r'''theory T imports Main begin
definition foo :: "nat" where "foo = 0"
lemma bar: "(0::nat) = 0" using foo_def by simp
end
'''

    def test_callers_stays_fact_level(self):
        sec = section_from(self.THY, "T")
        graph = cli._build_call_graph([sec])          # no derived resolution
        self.assertNotIn("bar", graph.callers["foo"])

    def test_unused_resolves_the_derived_spelling(self):
        sec = section_from(self.THY, "T")
        self.assertNotIn("foo", _unused(sec))


class OracleParity(unittest.TestCase):
    """The fast builder must still agree with the brute-force reference — in
    BOTH modes.  No pre-existing fixture had a top-level command citing a
    bare name, so the `<toplevel>` attribution slipped past the oracle
    entirely while every test still passed.  These pin both sides."""

    TOPLEVEL = r'''theory T imports Main begin

lemma bar: "(0::nat) = 0" by simp

lemmas bar_alias [simp] = bar

end
'''

    def assertParity(self, sections, derived):
        fast = cli._build_call_graph(sections, derived=derived)
        ref = brute_force_call_graph(sections, derived=derived)
        self.assertEqual(fast.callers, ref.callers)
        self.assertEqual(fast.callees, ref.callees)

    def test_toplevel_citation_matches_oracle(self):
        sec = section_from(self.TOPLEVEL, "T")
        # The citation is a `lemmas` line owned by no entry.
        self.assertIn("T:<toplevel>", cli._build_call_graph([sec]).callers["bar"])
        self.assertParity([sec], derived=False)

    def test_instantiation_matches_oracle_in_both_modes(self):
        sec = section_from(INSTANTIATION, "T")
        self.assertParity([sec], derived=False)
        self.assertParity([sec], derived=True)

    def test_derived_mode_only_adds_edges(self):
        sec = section_from(DeadnessVersusFactIdentity.THY, "T")
        plain = cli._build_call_graph([sec]).callers
        withd = cli._build_call_graph([sec], derived=True).callers
        for name, callers in plain.items():
            self.assertTrue(callers <= withd[name])   # monotone: never loses an edge
        self.assertNotEqual(plain, withd)             # and on this fixture, gains one


if __name__ == "__main__":
    unittest.main()
