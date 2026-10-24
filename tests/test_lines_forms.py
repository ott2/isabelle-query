"""`lines` accepts both `FILE RANGE...` and colon-form `FILE:RANGE ...`.

The colon form is the `enclosing` locus grammar reused: a span printed by
`outline` / `largest` / `enclosing` (now `A..B`) pastes back into `lines` as
`FILE:A..B`.  Both forms coexist.  The colon batch may name several files
[lines-files] (#33), each run of them under a header naming the file.
"""

import contextlib
import io
import os
import sys
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from support import cli  # noqa: E402

OWNERS = os.path.join(os.path.dirname(__file__), "fixtures", "Owners.thy")
NESTED = os.path.join(os.path.dirname(__file__), "fixtures", "Nested.thy")


def _run_lines(argv):
    parser = cli._build_parser()
    ns = parser.parse_args(["lines"] + argv)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        cli._run_lines(ns)
    return buf.getvalue()


class FileAndRangesSplit(unittest.TestCase):

    def test_classic_form(self):
        self.assertEqual(
            cli._lines_groups(["Foo", "1..10", "20..30"]),
            [("Foo", ["1..10", "20..30"])])

    def test_colon_form_one_file(self):
        self.assertEqual(
            cli._lines_groups(["Foo:1..10", "Foo:20..30"]),
            [("Foo", ["1..10", "20..30"])])

    def test_colon_form_single_line(self):
        # `Foo:6` is the `A..B` form with A == B.
        self.assertEqual(cli._lines_groups(["Foo:6"]),
                         [("Foo", ["6..6"])])

    def test_colon_form_several_files_in_order(self):
        self.assertEqual(
            cli._lines_groups(["A:1..2", "B:3", "B:5..", "A:7"]),
            [("A", ["1..2"]), ("B", ["3..3", "5.."]), ("A", ["7..7"])])


class EndToEnd(unittest.TestCase):

    def test_classic_and_colon_agree(self):
        classic = _run_lines([OWNERS, "5..6"])
        colon = _run_lines([f"{OWNERS}:5..6"])
        self.assertEqual(classic, colon)
        self.assertIn("definition widget :: nat where", classic)

    def test_colon_multi_range_one_file(self):
        out = _run_lines([f"{OWNERS}:5..6", f"{OWNERS}:15..16"])
        self.assertIn("definition widget :: nat where", out)   # line 5
        self.assertIn("lemma comm_add", out)                   # line 15
        self.assertIn("--", out)                               # range separator
        self.assertNotIn("==>", out)                           # one file

    def test_several_files_each_under_a_header(self):
        # The issue's case: one call for a list that spans files.
        out = _run_lines([f"{OWNERS}:5", f"{NESTED}:3"])
        self.assertEqual(out.splitlines(), [
            f"==> {OWNERS} <==",
            "5| definition widget :: nat where",
            "--",
            f"==> {NESTED} <==",
            '3| lemma flat: "True"',
        ])

    def test_an_unknown_file_fails_the_batch(self):
        # All or nothing: nothing printed, every unknown file named, exit 1.
        ns = cli._build_parser().parse_args(
            ["lines", f"{OWNERS}:5", "/no/such/A.thy:1", "/no/such/B.thy:2"])
        out, err = io.StringIO(), io.StringIO()
        cli._ROOT_OVERRIDE = Path(OWNERS).parent
        try:
            with contextlib.redirect_stdout(out), \
                    contextlib.redirect_stderr(err), \
                    self.assertRaises(SystemExit) as cm:
                cli._run_lines(ns)
        finally:
            cli._ROOT_OVERRIDE = None
        self.assertEqual(cm.exception.code, 1)
        self.assertEqual(out.getvalue(), "")
        self.assertIn("A.thy", err.getvalue())
        self.assertIn("B.thy", err.getvalue())


class Errors(unittest.TestCase):

    def test_mixed_forms_rejected(self):
        with self.assertRaises(SystemExit):
            cli._lines_groups(["A:1..2", "3..4"])

    def test_no_range_rejected(self):
        with self.assertRaises(SystemExit):
            cli._lines_groups(["Foo"])


if __name__ == "__main__":
    unittest.main()
