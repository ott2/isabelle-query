r"""A name an entry BINDS is a declaration of it, for reachability.

`graph._Visibility` scopes a citation to the theories that can SEE its
declaration (`test_citation_reach.py`).  It indexed declarations by ENTRY
name, so a datatype constructor, a `shows` conjunct or a mutually declared
constant — names Isabelle binds without an entry of their own — were declared
NOWHERE as far as the filter knew, and a name declared nowhere is never
filtered.  `callers Bar` therefore reported every theory that wrote `Bar`,
including one that could not have meant this `Bar` because it never imports
the datatype.

Isabelle binds `Bar` in the theory that writes `datatype colour = Bar | Baz`,
and a theory that does not import it cannot write that `Bar` either.  So the
single-name text scan counts an entry's bound names as declarations
[bound-name-reach].  The bulk call graph does not: its nodes are entries only,
so `callers -r` / `callees` / `refs` / `unused` / `graph citation` are
untouched, and this file pins that as well as the drop.

Real files, because the filter reads `imports` clauses off disk.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli, graph  # noqa: E402
from isabelle_query.commands import _find_callers  # noqa: E402

X = ('theory X imports Main begin\n'
     '  datatype colour = Bar | Baz\n'
     '  locale rev = fixes r :: nat\n'
     'end\n')
# Z imports X, so its `Bar` can be X's constructor.
Z = ('theory Z imports X begin\n'
     '  lemma z_mentions_bar: "Bar = Bar" by simp\n'
     'end\n')
# W does not import X: its `Bar` is something else of the same spelling.
W = ('theory W imports Main begin\n'
     '  lemma w_mentions_bar: "Bar = Bar" by simp\n'
     'end\n')


class BoundNameFixture(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        for name, text in (("X", X), ("Z", Z), ("W", W)):
            (self.dir / f"{name}.thy").write_text(text, encoding="utf-8")
        (self.dir / "ROOT").write_text(
            "session Demo = HOL +\n  theories\n    X\n    Z\n    W\n",
            encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def theories_citing(self, name, reach="closure"):
        return {s.theory for s, _ln, _txt in
                _find_callers(self.sections, name, reach=reach)}


class ABoundNameIsADeclaration(BoundNameFixture):

    def test_the_fixture_binds_bar_without_an_entry(self):
        # Non-vacuity: `Bar` must be a BOUND name, not an entry, or the test
        # would be pinning the entry rule `test_citation_reach.py` already
        # pins.
        names = {e.name for s in self.sections for e in s.entries}
        bound = {n for s in self.sections for e in s.entries
                 for n in e.bound_names}
        self.assertNotIn("Bar", names)
        self.assertIn("Bar", bound)

    def test_callers_of_a_constructor_are_scoped(self):
        self.assertEqual(self.theories_citing("Bar"), {"Z"})

    def test_name_mode_restores_the_unscoped_answer(self):
        self.assertEqual(self.theories_citing("Bar", reach="name"),
                         {"Z", "W"})

    def test_declared_in_knows_the_binder_only_when_asked(self):
        self.assertNotIn("Bar", graph._Visibility(self.sections).declared_in)
        vis = graph._Visibility(self.sections, bound_names=True)
        self.assertEqual(vis.declared_in["Bar"], {"X"})
        # An entry is declared where it was before, either way.
        self.assertEqual(vis.declared_in["colour"], {"X"})


class TheFacadeDecidesPerTheory(BoundNameFixture):

    def test_a_bound_name_is_admitted_where_it_is_visible(self):
        admits = graph.site_filter(self.sections, "Bar")
        self.assertTrue(admits("X"))
        self.assertTrue(admits("Z"))
        self.assertFalse(admits("W"))

    def test_an_entry_is_admitted_the_same_way(self):
        admits = graph.site_filter(self.sections, "colour")
        self.assertTrue(admits("Z"))
        self.assertFalse(admits("W"))

    def test_name_mode_admits_everything(self):
        admits = graph.site_filter(self.sections, "Bar", reach="name")
        self.assertTrue(admits("W"))

    def test_a_name_declared_nowhere_admits_everything(self):
        # Nothing to scope to, so nothing is dropped — and no closure is
        # built to find that out.
        admits = graph.site_filter(self.sections, "nothing_declares_this")
        self.assertTrue(admits("W"))
        self.assertTrue(admits("No_Such_Theory"))


class TheBulkGraphIsUntouched(BoundNameFixture):

    def test_a_bound_name_is_not_a_node(self):
        g = graph._build_call_graph(self.sections)
        self.assertNotIn("Bar", g.all_names)
        self.assertNotIn("Bar", g.callers)

    def test_the_edge_set_is_the_hand_computed_one(self):
        # Nothing in the fixture cites an ENTRY by name: `Bar = Bar` names a
        # constructor, and `colour` / `rev` are written nowhere but their own
        # declarations.  So the graph has no edges at all, under both modes.
        for reach in ("closure", "name"):
            with self.subTest(reach=reach):
                g = graph._build_call_graph(self.sections, reach=reach)
                edges = {(c, n) for n, cs in g.callers.items() for c in cs}
                self.assertEqual(edges, set())


if __name__ == "__main__":
    unittest.main()
