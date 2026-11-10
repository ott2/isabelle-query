r"""`unused --assume-deleted S`: what deleting S takes with it (#39)
[assume-deleted].

The answer is the cascade seeded with S alone: an entry joins when every
citer is in S or has itself joined.  Nothing else counts as dead, so an
entry that an unused lemma OUTSIDE S also cites stays, because deleting it
would break that lemma.  A citation of S from outside S is a blocker:
listed, with exit status 3.

Hand-computed for the fixture (one theory, so declaration order is line
order):

    deep        cited by shared
    kept_dep    cited by shared, keeper (a theorem: evidence, live)
    simp_lem    [simp] (evidence), cited by r2
    also_stray  cited by shared, stray (uncited, not in S)
    lifted      cited by t_root (a theorem: live today)
    shared      cited by r1, r2
    only1       cited by r1
    used_root   cited by outsider (uncited)

S = {r1, r2}, -r:  pass 1 shared, only1;  pass 2 deep (kept_dep keeps
    keeper's citation, also_stray keeps stray's);  simp_lem is listed at
    depth 1 with its evidence, as `unused` lists such an entry.  Today's
    `unused -r` lists all four already, so none is `[freed]`.
S = {r1, r2}, no -r:  one level, shared, only1, simp_lem.
S + t_root:  also lifted, which `unused -r` does not list today: `[freed]`.
    The theorem's own evidence does not keep it, being named for deletion.
S = {r1, used_root}:  only1 (shared keeps r2's citation); blocker
    `used_root cited by outsider`, and outsider is itself unused.
"""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

from isabelle_query import cli

THY = """\
theory T
  imports Main
begin

lemma deep: "True" by simp
lemma kept_dep: "True" by simp
lemma simp_lem [simp]: "True" by simp
lemma also_stray: "True" by simp
lemma lifted: "True" by simp
lemma shared: "True" using deep kept_dep also_stray by simp
lemma only1: "True" by simp
lemma r1: "True" using shared only1 by simp
lemma r2: "True" using shared simp_lem by simp
theorem keeper: "True" using kept_dep by simp
lemma stray: "True" using also_stray by simp
theorem t_root: "True" using lifted by simp
lemma used_root: "True" by simp
lemma outsider: "True" using used_root by simp

end
"""


class AssumeDeleted(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.d = Path(self._tmp.name)
        (self.d / "ROOT").write_text("session S = HOL +\n  theories T\n",
                                     encoding="utf-8")
        (self.d / "T.thy").write_text(THY, encoding="utf-8")

    def tearDown(self):
        self._tmp.cleanup()

    def run_cli(self, *args):
        out, err = io.StringIO(), io.StringIO()
        old = sys.argv
        sys.argv = ["query", "-R", str(self.d), *args]
        code = 0
        try:
            with contextlib.redirect_stdout(out), \
                 contextlib.redirect_stderr(err):
                try:
                    cli.main()
                except SystemExit as e:
                    code = e.code or 0
        finally:
            sys.argv = old
        return code, out.getvalue(), err.getvalue()

    def rows(self, *args):
        code, out, err = self.run_cli("unused", "--names", *args)
        return code, [ln.split(None, 3)[1:] for ln in out.splitlines()], err

    def test_the_set_drags_its_exclusive_cascade(self):
        code, rows, _ = self.rows("-r", "--assume-deleted", "r1,r2")
        self.assertEqual(code, 0)
        self.assertEqual(rows, [                    # in source order
            ["deep", "T", "[cascade depth 2]"],
            ["simp_lem", "T", "[cascade depth 1]  [evidence: simp]"],
            ["shared", "T", "[cascade depth 1]"],
            ["only1", "T", "[cascade depth 1]"]])

    def test_repeated_flags_and_a_file_are_one_set(self):
        (self.d / "del").write_text("# the chain\nT r1  root one\nT r2\n",
                                    encoding="utf-8")
        want = self.rows("-r", "--assume-deleted", "r1,r2")
        self.assertEqual(self.rows("-r", "--assume-deleted", "r1",
                                   "--assume-deleted", "r2"), want)
        self.assertEqual(self.rows("-r", "--assume-deleted-file",
                                   str(self.d / "del")), want)

    def test_without_r_it_is_one_level(self):
        _, rows, _ = self.rows("--assume-deleted", "r1,r2")
        self.assertEqual([r[0] for r in rows],
                         ["simp_lem", "shared", "only1"])
        self.assertTrue(all("depth" not in r[-1] for r in rows))

    def test_live_today_is_freed(self):
        _, rows, _ = self.rows("-r", "--assume-deleted", "r1,r2,t_root")
        self.assertIn(["lifted", "T", "[cascade depth 1]  [freed]"], rows)
        self.assertEqual(sum("[freed]" in r[-1] for r in rows), 1)

    def test_a_deleted_name_overrides_keep(self):
        # The same rows, but now `[freed]`: with r1 kept, today's
        # `unused -r` keeps its subtree too.
        _, kept, _ = self.rows("-r", "--keep", "r1",
                               "--assume-deleted", "r1,r2")
        _, plain, _ = self.rows("-r", "--assume-deleted", "r1,r2")
        self.assertEqual([r[0] for r in kept], [r[0] for r in plain])
        self.assertEqual([r[0] for r in kept if "[freed]" in r[-1]],
                         ["deep", "shared", "only1"])

    def test_the_header(self):
        code, out, _ = self.run_cli("unused", "-r",
                                    "--assume-deleted", "r1,r2,t_root")
        self.assertEqual(code, 0)
        self.assertEqual(out.splitlines()[0],
                         "Deleting 3 entries takes 5 more with it (4 cited "
                         "only from the set + 1 cascading, 5 source lines, "
                         "1 freed by the deletion, 1 of them with evidence):")

    def test_nothing_dragged(self):
        code, out, _ = self.run_cli("unused", "--assume-deleted", "stray")
        self.assertEqual((code, out),
                         (0, "Deleting 1 entry takes nothing else with it.\n"))

    def test_a_citation_from_outside_blocks(self):
        code, out, err = self.run_cli("unused", "-r",
                                      "--assume-deleted", "r1,used_root")
        self.assertEqual((code, err), (3, ""))
        lines = out.splitlines()
        self.assertEqual(lines[0], "1 entry to delete is still cited from "
                                   "outside the set (1 citation):")
        self.assertEqual(lines[2].split(),
                         ["used_root", "cited", "by", "outsider", "T",
                          "[unused]"])
        self.assertTrue(any(ln.split()[1:2] == ["only1"] for ln in lines))

    def test_blockers_go_to_stderr_when_stdout_is_for_scripts(self):
        code, out, err = self.run_cli("unused", "-r", "-c",
                                      "--assume-deleted", "r1,used_root")
        self.assertEqual((code, out), (3, "1\n"))
        self.assertIn("used_root  cited by  outsider", err)
        code, out, err = self.run_cli("unused", "-r", "--names",
                                      "--assume-deleted", "r1,used_root")
        self.assertEqual((code, [ln.split()[1] for ln in out.splitlines()]),
                         (3, ["only1"]))
        self.assertIn("cited by", err)

    def test_an_unknown_name_is_an_error(self):
        code, out, err = self.run_cli("unused", "--assume-deleted",
                                      "r1,nosuch,nope")
        self.assertEqual((code, out), (1, ""))
        self.assertIn("'nosuch'", err)
        self.assertIn("'nope'", err)
        (self.d / "del").write_text("T r1\nT nosuch\n", encoding="utf-8")
        code, out, err = self.run_cli("unused", "--assume-deleted-file",
                                      str(self.d / "del"))
        self.assertEqual((code, out), (1, ""))
        self.assertIn(":2: T declares no 'nosuch'", err)

    def test_usage_errors(self):
        self.assertEqual(self.run_cli("unused", "--roots",
                                      "--assume-deleted", "r1")[0], 2)
        self.assertEqual(self.run_cli("unused", "facts",
                                      "--assume-deleted", "r1")[0], 2)
        self.assertEqual(self.run_cli("unused", "--assume-deleted-file",
                                      str(self.d / "missing"))[0], 2)

    def test_without_the_option_nothing_changes(self):
        code, rows, _ = self.rows("-r")
        self.assertEqual(code, 0)
        self.assertNotIn("[freed]", " ".join(r[-1] for r in rows))


if __name__ == "__main__":
    unittest.main()
