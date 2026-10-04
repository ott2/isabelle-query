"""Version-keyed namespace resolver (`isabelle_query._namespace_resolve`).

The cache buys "always up to date" without the per-invocation Isabelle tax: a
spawn-free fingerprint of the session heap decides validity, so the warm path is
a file read and Isabelle is touched only when the heap actually changes.  These
tests are hermetic — no Isabelle, no network: a fake heap file drives the
fingerprint, and the dump is stubbed to prove the cache-hit path never spawns.

The module under test is the *package* resolver (not the `scripts/` front-end):
`resolve_namespace` calls `dump` / `_heap_file` / `isabelle_fingerprint` as
module-local names, so the `mock.patch.object(nc, ...)` stubs must target that
same module or the real subprocess would run.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, os.path.dirname(__file__))
from support import cli  # noqa: E402,F401  (puts src/ on the path)
import isabelle_query._namespace_resolve as nc  # noqa: E402


class CacheRoundTrip(unittest.TestCase):
    def test_save_then_load(self):
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}):
                payload = {"fingerprint": "abc", "session": "HOL",
                           "methods": ["auto", "simp"], "attributes": ["OF"]}
                nc.save_cache("HOL", payload)
                self.assertEqual(nc.load_cache("HOL"), payload)

    def test_load_missing_is_none(self):
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}):
                self.assertIsNone(nc.load_cache("HOL"))


class Fingerprint(unittest.TestCase):
    """The fingerprint is a pure `stat` — spawn-free, and sensitive to a heap
    that has been rebuilt (size or mtime changed)."""

    def _fake_install(self, tmp: str, version: str = "Isabelle2099-9"):
        # a fake `isabelle` binary whose path carries the version id ...
        binp = Path(tmp) / f"{version}.app" / "bin" / "isabelle"
        binp.parent.mkdir(parents=True)
        binp.write_text("#!/bin/sh\n")
        # ... and a fake session heap under ISABELLE_HEAPS/<plat>/HOL.
        heap = Path(tmp) / "heaps" / "plat" / "HOL"
        heap.parent.mkdir(parents=True)
        heap.write_bytes(b"HEAP-V1")
        return str(binp), heap

    def test_spawn_free(self):
        # even if every subprocess call would explode, the fingerprint computes:
        # it only stats the filesystem.
        with tempfile.TemporaryDirectory() as tmp:
            binp, heap = self._fake_install(tmp)
            with mock.patch.dict(os.environ,
                                 {"ISABELLE_HEAPS": str(heap.parent.parent)}), \
                 mock.patch("subprocess.run",
                            side_effect=AssertionError("spawned!")):
                fp = nc.isabelle_fingerprint("HOL", isabelle=binp)
                self.assertTrue(fp)

    def test_changes_when_heap_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            binp, heap = self._fake_install(tmp)
            with mock.patch.dict(os.environ,
                                 {"ISABELLE_HEAPS": str(heap.parent.parent)}):
                fp1 = nc.isabelle_fingerprint("HOL", isabelle=binp)
                heap.write_bytes(b"HEAP-V2-longer")   # rebuilt: size + mtime move
                fp2 = nc.isabelle_fingerprint("HOL", isabelle=binp)
                self.assertNotEqual(fp1, fp2)

    def test_empty_without_isabelle(self):
        self.assertEqual(
            nc.isabelle_fingerprint("HOL", isabelle="/no/such/isabelle"), "")


class Resolve(unittest.TestCase):
    def test_falls_back_to_committed(self):
        # allow_isabelle=False forces the no-Isabelle path -> the committed set.
        from isabelle_query._isabelle_namespace import (
            ATTRIBUTES, PROOF_METHODS)
        r = nc.resolve_namespace("HOL", allow_isabelle=False)
        self.assertEqual(r["source"], "committed")
        self.assertEqual(r["methods"], PROOF_METHODS)
        self.assertEqual(r["attributes"], ATTRIBUTES)

    def test_cache_hit_does_not_spawn(self):
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   return_value="FP"), \
                 mock.patch.object(nc, "dump",
                                   side_effect=AssertionError("dumped!")):
                nc.save_cache("HOL", {"fingerprint": "FP", "theory": "Main",
                                      "methods": ["simp"], "attributes": ["OF"]})
                r = nc.resolve_namespace("HOL")
                self.assertEqual(r["source"], "cache")
                self.assertEqual(r["methods"], frozenset({"simp"}))

    def test_cache_miss_regenerates_and_base_folds(self):
        with tempfile.TemporaryDirectory() as d:
            # dump returns extern-qualified names; resolve must base-fold them.
            fake = ({"HOL.simp", "induction"}, {"HOL.dest", "OF"}, "Main", None)
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   return_value="FP2"), \
                 mock.patch.object(nc, "dump", return_value=fake):
                r = nc.resolve_namespace("HOL")
                self.assertEqual(r["source"], "isabelle")
                self.assertEqual(r["methods"], frozenset({"simp", "induction"}))
                self.assertEqual(r["attributes"], frozenset({"dest", "OF"}))
                # and it was memoised under the new fingerprint
                self.assertEqual(nc.load_cache("HOL")["fingerprint"], "FP2")


class AFailedDumpIsNotRepeated(unittest.TestCase):
    """A dump that failed against these heaps is not re-run [stale-heap-dump].

    Only a successful dump was cached, so a session whose heap Isabelle cannot
    load — a child built before its parent was rebuilt, or one whose parent's
    heap is missing — spawned Isabelle on every invocation, 1.6 s each, and two
    such sessions were 3.3 s of a 5.3 s warm `callers -r`.  The failure is now
    recorded against the session fingerprint AND the state of every heap, since
    rebuilding the parent is what clears it.
    """

    FAILED = (set(), set(), None,
              mock.Mock(returncode=1, stdout="",
                        stderr='Exception- Fail "The parent for this saved '
                               'state does not match"'))

    def _resolve(self, dump, heaps="H1"):
        with mock.patch.object(nc, "isabelle_fingerprint", return_value="FP"), \
             mock.patch.object(nc, "_heap_file", return_value=Path("/h")), \
             mock.patch.object(nc, "_heaps_state", return_value=heaps), \
             mock.patch.object(nc, "dump", dump):
            return nc.resolve_namespace("Child")

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self._env = mock.patch.dict(os.environ,
                                    {"QUERY_CACHE_DIR": self._tmp.name})
        self._env.start()

    def tearDown(self):
        self._env.stop()
        self._tmp.cleanup()

    def test_the_second_call_does_not_spawn(self):
        first = mock.Mock(return_value=self.FAILED)
        self.assertEqual(self._resolve(first)["source"], "committed")
        self.assertEqual(first.call_count, 1)
        again = mock.Mock(side_effect=AssertionError("dumped again"))
        self.assertEqual(self._resolve(again)["source"], "committed")

    def test_a_changed_heap_retries(self):
        self._resolve(mock.Mock(return_value=self.FAILED), heaps="H1")
        ok = mock.Mock(return_value=({"simp"}, {"OF"}, "Main", None))
        r = self._resolve(ok, heaps="H2")    # e.g. the parent was rebuilt
        self.assertEqual(ok.call_count, 1)
        self.assertEqual(r["source"], "isabelle")

    def test_a_timeout_is_not_recorded(self):
        # `dump` returns process None on a timeout, which may be load on the
        # machine rather than anything about the heaps.
        timed_out = (set(), set(), None, None)
        self._resolve(mock.Mock(return_value=timed_out))
        retry = mock.Mock(return_value=timed_out)
        self._resolve(retry)
        self.assertEqual(retry.call_count, 1)


class Augmented(unittest.TestCase):
    """Two-tier resolution: base unioned with a session's active table, and the
    no-build guarantee (a session with no heap is skipped, never built)."""

    def test_unions_base_and_session(self):
        dumps = {"HOL": ({"simp"}, {"OF"}, "Main", None),
                 "HOL-Analysis": ({"measurable"}, {"bounded_linear"},
                                  "Analysis", None)}
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "_heap_file",
                                   side_effect=lambda vid, s: Path("/fake") / s), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   side_effect=lambda s, isabelle=None: "FP-" + s), \
                 mock.patch.object(nc, "dump",
                                   side_effect=lambda s, dirs=None: dumps[s]):
                r = nc.resolve_augmented("HOL-Analysis", base="HOL")
                self.assertEqual(r["augmented_with"], "HOL-Analysis")
                self.assertEqual(r["methods"], frozenset({"simp", "measurable"}))
                self.assertEqual(r["attributes"],
                                 frozenset({"OF", "bounded_linear"}))

    def test_no_build_when_session_heap_absent(self):
        # the augmenting session has no heap -> it must be skipped, and dump()
        # (which would build it) must never be called.
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   side_effect=lambda s, isabelle=None: "FP-" + s), \
                 mock.patch.object(nc, "_heap_file", return_value=None), \
                 mock.patch.object(nc, "dump",
                                   side_effect=AssertionError("built a heap!")):
                nc.save_cache("HOL", {"fingerprint": "FP-HOL", "theory": "Main",
                                      "methods": ["simp"], "attributes": ["OF"]})
                r = nc.resolve_augmented("Some_Unbuilt_Session", base="HOL")
                self.assertIsNone(r["augmented_with"])
                self.assertEqual(r["methods"], frozenset({"simp"}))

    def test_skips_when_session_is_base(self):
        r = nc.resolve_augmented("HOL", base="HOL", allow_isabelle=False)
        self.assertIsNone(r["augmented_with"])
        self.assertEqual(r["source"], "committed")


class ProjectResolution(unittest.TestCase):
    """`resolve_project`: the union of the dumped tables of the project's *built*
    sessions over the committed (Pure) floor — no HOL base injected.  Unbuilt and
    duplicate sessions are skipped; the built-session set is one glob, not one per
    declared session; with no built session (or no Isabelle) the committed table
    is the fallback."""

    def test_unions_committed_floor_with_built_sessions(self):
        committed_m, committed_a = nc._committed()
        dumps = {"Nominal2": ({"eqvt"}, {"eqvt_def"}, "Nominal", None)}
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   side_effect=lambda s, isabelle=None: "FP-" + s), \
                 mock.patch.object(nc, "_heap_file",
                                   side_effect=lambda vid, s: Path("/fake") / s), \
                 mock.patch.object(nc, "_built_sessions",
                                   return_value={"Nominal2"}), \
                 mock.patch.object(nc, "dump",
                                   side_effect=lambda s, dirs=None: dumps[s]):
                # HOLCF is declared but unbuilt; Nominal2 repeats.
                r = nc.resolve_project(["Nominal2", "HOLCF", "Nominal2"])
                self.assertEqual(r["sessions"], ["Nominal2"])
                self.assertEqual(r["source"], "isabelle:Nominal2")
                # committed floor is kept, and the built session's table added.
                self.assertIn("eqvt", r["methods"])
                self.assertIn("eqvt_def", r["attributes"])
                self.assertTrue(r["methods"] >= committed_m)
                self.assertTrue(r["attributes"] >= committed_a)

    def test_no_built_session_returns_committed(self):
        committed_m, _ = nc._committed()
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "_built_sessions", return_value={"HOL"}), \
                 mock.patch.object(nc, "dump",
                                   side_effect=AssertionError("dumped unbuilt!")):
                r = nc.resolve_project(["HOLCF", "Nominal2"])
                self.assertIsNone(r["sessions"])
                self.assertEqual(r["source"], "committed")
                self.assertEqual(r["methods"], committed_m)

    def test_no_isabelle_returns_committed_without_glob(self):
        # allow_isabelle=False must not even probe the heaps dir.
        with mock.patch.object(nc, "_built_sessions",
                               side_effect=AssertionError("globbed heaps!")):
            r = nc.resolve_project(["Nominal2"], allow_isabelle=False)
            self.assertIsNone(r["sessions"])
            self.assertEqual(r["source"], "committed")

    def test_failed_dump_reports_committed_not_isabelle(self):
        # A *built* session whose dump FAILS (empty tables — e.g. the session is
        # unknown to `ML_process -l` for lack of its ROOT dir) degrades to the
        # committed floor.  It must NOT be counted as folded-in: the floor is
        # always non-empty, so gating on non-empty methods would mis-report the
        # failure as `isabelle:<session>` and suppress the Pure-fallback warning.
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   side_effect=lambda s, isabelle=None: "FP-" + s), \
                 mock.patch.object(nc, "_heap_file",
                                   side_effect=lambda vid, s: Path("/fake") / s), \
                 mock.patch.object(nc, "_built_sessions",
                                   return_value={"Cook_Levin"}), \
                 mock.patch.object(nc, "dump",
                                   side_effect=lambda s, dirs=None:
                                   (set(), set(), None, None)):
                r = nc.resolve_project(["Cook_Levin"])
                self.assertEqual(r["source"], "committed")
                self.assertIsNone(r["sessions"])

    def test_forwards_dirs_to_dump(self):
        # The project's ROOT dirs must reach the dump — that is what makes a
        # project/AFP session resolvable by name.
        seen = {}

        def fake_dump(s, dirs=None):
            seen["dirs"] = dirs
            return ({"m"}, {"a"}, "T", None)

        with tempfile.TemporaryDirectory() as d:
            with mock.patch.dict(os.environ, {"QUERY_CACHE_DIR": d}), \
                 mock.patch.object(nc, "isabelle_fingerprint",
                                   side_effect=lambda s, isabelle=None: "FP-" + s), \
                 mock.patch.object(nc, "_heap_file",
                                   side_effect=lambda vid, s: Path("/fake") / s), \
                 mock.patch.object(nc, "_built_sessions", return_value={"S"}), \
                 mock.patch.object(nc, "dump", side_effect=fake_dump):
                nc.resolve_project(["S"], dirs=["/proj/root"])
                self.assertEqual(seen["dirs"], ["/proj/root"])


if __name__ == "__main__":
    unittest.main()
