"""`-i` / `--ignore-case` on the search verbs (issue #13).

On `grep` it is `re.IGNORECASE`, which is what a leading `(?i)` already
spelled, and it composes with the `\\|` rewrite.  `find` has always matched
without regard to case, so there `-i` is accepted and changes nothing — the
same contract as `-n` (`test_cli_names_flag`).

The fixture's counts are hand-read: `Hennie` is written once capitalised
(line 5, a lemma name) and once lower-case (line 7, in `using`), and `foo`
once (line 7).
"""

import io
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from support import cli  # noqa: E402

CASE_FIX = r'''theory Case_Fix
  imports Main
begin

lemma Hennie_bound: "True" by simp

lemma other: "True" using hennie_bound foo by simp

end
'''


class GrepIgnoreCase(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "Case_Fix.thy").write_text(CASE_FIX, encoding="utf-8")
        (d / "ROOT").write_text(
            "session Fix = HOL +\n  theories\n    Case_Fix\n",
            encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()
        self.parser = cli._build_parser()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def count(self, *argv):
        ns = self.parser.parse_args(["grep", *argv, "-c"])
        out = io.StringIO()
        with redirect_stdout(out):
            cli.cmd_grep(self.sections, ns.pattern, cli._flags_from_ns(ns))
        return int(out.getvalue())

    def test_case_sensitive_by_default(self):
        self.assertEqual(self.count("hennie"), 1)

    def test_both_spellings_ignore_case(self):
        self.assertEqual(self.count("hennie", "-i"), 2)
        self.assertEqual(self.count("hennie", "--ignore-case"), 2)

    def test_it_is_the_inline_flag(self):
        self.assertEqual(self.count("hennie", "-i"),
                         self.count("(?i)hennie"))

    def test_it_composes_with_the_alternation_rewrite(self):
        # Lines 5 and 7; `FOO` alone would match nothing.
        self.assertEqual(self.count(r"HENNIE\|FOO", "-i"), 2)


class FindAcceptsIt(unittest.TestCase):

    def test_find_parses_identically_to_its_absence(self):
        parser = cli._build_parser()
        for flag in ("-i", "--ignore-case"):
            with self.subTest(flag=flag):
                self.assertEqual(parser.parse_args(["find", "x"]),
                                 parser.parse_args(["find", "x", flag]))


if __name__ == "__main__":
    unittest.main()
