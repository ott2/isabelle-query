r"""`api.resolve_theories` reads a locus's THEORY as the CLI does (#34)
[theory-candidates].

A tool that edits a `THEORY:A..B` span query printed must land in the file
query meant.  query's own history records the failure when reader and
printer disagree: `beta/Examples` resolved to `alpha/Examples`, silently
[disambig-names].  So the library reads loci through the CLI's own tiers,
and returns every candidate, so that an editor can refuse an ambiguous one.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import api, cli  # noqa: E402
from isabelle_query.commands import _resolve_theory  # noqa: E402
from isabelle_query.render import theory_labels  # noqa: E402

THY = 'theory {name}\nimports Main\nbegin\nlemma l{tag}: "True" by simp\nend\n'


class _Corpus(unittest.TestCase):
    """LAYOUT: entry directory -> [(theory as its ROOT spells it, file)]."""

    LAYOUT: dict = {}

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name).resolve()
        tag = 0
        for entry, theories in self.LAYOUT.items():
            for spelled, rel in theories:
                p = self.dir / entry / f"{rel}.thy"
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(THY.format(name=Path(rel).name, tag=tag),
                             encoding="utf-8")
                tag += 1
            names = "\n    ".join(s for s, _ in theories)
            (self.dir / entry / "ROOT").write_text(
                f"session {entry} = HOL +\n  theories\n    {names}\n",
                encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def resolve(self, *names):
        return api.resolve_theories(list(names), root=self.dir)

    def file(self, rel):
        return self.dir / f"{rel}.thy"


class ACorpusWithASharedName(_Corpus):

    LAYOUT = {"alpha": [("Examples", "Examples"), ("Unique", "Unique")],
              "beta": [("Examples", "Examples")]}

    def test_every_printed_label_reads_back_to_its_own_file(self):
        labels = theory_labels(self.sections)
        self.assertIn("beta/Examples", labels.values())
        got = self.resolve(*labels.values())
        for path, label in labels.items():
            with self.subTest(label):
                self.assertEqual(got[label], [path])

    def test_a_shared_bare_name_lists_every_theory(self):
        # The CLI reads the first; an editor sees there were two.
        got = self.resolve("Examples")["Examples"]
        self.assertEqual(sorted(got), [self.file("alpha/Examples"),
                                       self.file("beta/Examples")])
        self.assertEqual(got[0],
                         _resolve_theory(self.sections, "Examples").path
                         .resolve())

    def test_a_path_and_a_unique_name(self):
        got = self.resolve(str(self.file("beta/Examples")), "Unique")
        self.assertEqual(got[str(self.file("beta/Examples"))],
                         [self.file("beta/Examples")])
        self.assertEqual(got["Unique"], [self.file("alpha/Unique")])

    def test_no_such_theory_is_an_empty_list(self):
        self.assertEqual(self.resolve("Nope", "gamma/Examples"),
                         {"Nope": [], "gamma/Examples": []})

    def test_no_guesses_for_a_writer(self):
        # The CLI's two last resorts, which can name ONE wrong file: the stem
        # of a label that matched nothing, and a case-folded name.
        for name in ("gamma/Unique", "unique"):
            with self.subTest(name):
                self.assertIsNotNone(_resolve_theory(self.sections, name))
                self.assertEqual(self.resolve(name), {name: []})


class APathSpelledName(_Corpus):
    """The AFP shape behind [label-depth]: a copy NAMED `SL/Automation`."""

    LAYOUT = {"SL": [("Automation", "Automation")],
              "Other": [("Automation", "Automation")],
              "VEB": [('"SL/Automation"', "SL/Automation")],
              "VEB2": [('"SL/Automation"', "SL/Automation")]}

    def test_every_printed_label_reads_back_to_its_own_file(self):
        labels = theory_labels(self.sections)
        got = self.resolve(*labels.values())
        for path, label in labels.items():
            with self.subTest(label):
                self.assertEqual(got[label], [path])

    def test_the_name_lists_both_copies(self):
        got = self.resolve("SL/Automation")["SL/Automation"]
        self.assertEqual(sorted(got), [self.file("VEB/SL/Automation"),
                                       self.file("VEB2/SL/Automation")])


class TheRoot(_Corpus):

    LAYOUT = {"alpha": [("Unique", "Unique")]}

    def test_found_as_the_cli_finds_it(self):
        env = {"ISABELLE_QUERY_ROOT": str(self.dir)}
        with mock.patch.dict(os.environ, env), \
                mock.patch.dict(os.environ, {"ISABELLE_LAYOUT_ROOT": ""}):
            self.assertEqual(api.resolve_theories(["Unique"]),
                             {"Unique": [self.file("alpha/Unique")]})

    def test_a_bad_root_raises_as_parse_root_does(self):
        with self.assertRaises(ValueError):
            api.resolve_theories(["Unique"], root=self.dir / "nope")
        empty = self.dir / "empty"
        empty.mkdir()
        with self.assertRaises(ValueError):
            api.resolve_theories(["Unique"], root=empty)

    def test_one_string_is_refused_not_read_as_letters(self):
        with self.assertRaises(TypeError):
            api.resolve_theories("Unique", root=self.dir)


if __name__ == "__main__":
    unittest.main()
