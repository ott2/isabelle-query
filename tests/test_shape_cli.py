"""The `query shape` subcommand family — argparse wiring, the JSONL join
contract, and the ranking / scoping behaviour of the five views.

Unlike every other verb, `shape` is a *nested* subparser group
(`shape summary|steps|lemma|widest|census`), so these tests pin both that the
nested dispatch reaches each `_run_shape_*` handler and that the record streams
carry the documented, stable schema (the contract downstream LLM-tractability
and phase-2 joins depend on).  Behaviour is checked against `Shape.thy`, whose
per-step values are hand-computed in `test_shape.py`.
"""

import argparse
import contextlib
import io
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import cli, section_from  # noqa: E402
from isabelle_query import shape, shape_cmds  # noqa: E402

FIXTURES = os.path.join(os.path.dirname(__file__), "fixtures")
with open(os.path.join(FIXTURES, "Shape.thy"), encoding="utf-8") as _fh:
    THY = _fh.read()


def _sec():
    return section_from(THY, "Shape")


def _run(fn, *args, **kw):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn(*args, **kw)
    return buf.getvalue()


def _jsonl(text):
    return [json.loads(ln) for ln in text.splitlines() if ln.strip()]


def _sub(parser, cmd):
    action = next(a for a in parser._actions
                  if isinstance(a, argparse._SubParsersAction))
    return action.choices[cmd]


def _wsub(parser, name):
    """The nested `shape NAME` subparser."""
    return _sub(_sub(parser, "shape"), name)


# -- argparse wiring --------------------------------------------------------

class Wiring(unittest.TestCase):
    def setUp(self):
        self.parser = cli._build_parser()

    def test_each_view_dispatches_to_its_handler(self):
        cases = {
            "summary": cli._run_shape_summary,
            "steps": cli._run_shape_steps,
            "lemma": cli._run_shape_lemma,
            "widest": cli._run_shape_widest,
            "census": cli._run_shape_census,
        }
        for name, handler in cases.items():
            with self.subTest(view=name):
                argv = ["shape", name] + (["x"] if name == "lemma" else [])
                ns = self.parser.parse_args(argv)
                self.assertIs(ns.func, handler)

    def test_bare_shape_has_a_help_fallback(self):
        # no subcommand chosen -> a func is still set (prints the group help),
        # so `main` does not fall through to the top-level parser.
        ns = self.parser.parse_args(["shape"])
        self.assertTrue(callable(ns.func))

    def test_lemma_is_variadic_lookup(self):
        ns = self.parser.parse_args(["shape", "lemma", "A", "B"])
        self.assertEqual(ns.name, ["A", "B"])

    def test_widest_metric_is_constrained(self):
        ns = self.parser.parse_args(["shape", "widest", "--metric", "live"])
        self.assertEqual(ns.metric, "live")
        with self.assertRaises(SystemExit):
            self.parser.parse_args(["shape", "widest", "--metric", "bogus"])

    def test_widest_carries_trailing_paths(self):
        # search family: scoped by PATH positionals like `largest`.
        ns = self.parser.parse_args(["shape", "widest", "A.thy", "B.thy"])
        self.assertEqual(ns.files, ["A.thy", "B.thy"])

    def test_steps_span_is_optional(self):
        self.assertIsNone(self.parser.parse_args(["shape", "steps"]).span)
        self.assertEqual(
            self.parser.parse_args(["shape", "steps", "Foo:1..9"]).span,
            "Foo:1..9")

    def test_config_flags_only_on_record_views(self):
        for name in ("steps", "lemma"):
            self.assertTrue(any(a.dest == "config"
                                for a in _wsub(self.parser, name)._actions))
        # summary / widest / census do not take a corpus config.
        for name in ("summary", "widest", "census"):
            self.assertFalse(any(a.dest == "config"
                                 for a in _wsub(self.parser, name)._actions))


# -- JSONL schema (the join contract) ---------------------------------------

_STEP_KEYS = {
    "theory", "lemma", "line", "block", "depth", "kind", "kw", "goal_cmd",
    "method", "label", "stmt_start", "stmt_end", "w2_src", "w1_est", "col",
    "w1_schematic_est", "w1_bound_est", "const_est", "const_canon_est",
    "fanin", "fanin_covered", "live", "introduces", "consumes",
}
_SUMMARY_KEYS = {
    # `session` is provenance, `null` outside a session-aware load — a corpus
    # run needs it because AFP theory names are not unique across entries.
    "session",
    "theory", "lemma", "n_steps", "n_goals", "n_bare", "depth_max", "w2_src_max",
    "w2_src_mean", "w2_src_p90", "w1_est_max", "w1_est_mean",
    "const_est_max", "const_est_mean",
    "const_canon_est_max", "const_canon_est_mean", "fanin_max",
    "fanin_mean", "fanin_cited", "live_max", "live_mean", "dag_ratio_est_max",
    "introduce",
    "consume", "both", "ratio", "trivial_frac", "removable_w2_est_at_8",
    "method_kinds",
    # Why each of the `n_bare` steps is bare; the three keys sum to `n_bare`,
    # which is unchanged — a refinement, not a redefinition [bare-provenance].
    "bare_kinds",
    "n_induct", "induct_terms_max", "induct_arbitrary_max", "induct_rule",
    "induct_recursion",
    "proof_lines", "proof_lines_code", "proof_tokens", "proof_tokens_code",
    "entry_lines",
}


class StepJsonSchema(unittest.TestCase):
    def test_steps_json_keys_and_position(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                           span="Shape:62", as_json=True))
        self.assertEqual(len(recs), 1)
        rec = recs[0]
        self.assertEqual(set(rec), _STEP_KEYS)
        # stable position key + a hand-computed metric.
        self.assertEqual((rec["theory"], rec["lemma"], rec["line"]),
                         ("Shape", "redundant", 62))
        self.assertEqual(rec["w2_src"], 11)

    def test_all_steps_flag_widens_the_stream(self):
        goals = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                            span="Shape", as_json=True))
        every = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                            span="Shape", as_json=True, all_steps=True))
        self.assertTrue(all(r["kind"] == "goal" for r in goals))
        self.assertGreater(len(every), len(goals))
        self.assertTrue(any(r["kind"] == "closing" for r in every))

    def test_config_gates_frame_columns(self):
        cfg = shape.load_corpus_config(
            os.path.join(FIXTURES, "m3_configs.toml"))["Shape"]
        without = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                              span="Shape:92", as_json=True))[0]
        withcfg = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                              span="Shape:92", as_json=True, cfg=cfg))[0]
        self.assertNotIn("frame_ratio", without)
        self.assertEqual(withcfg["frame_ratio"], 5.0)     # m3_wide

    def test_widest_json_is_ranked_records(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_widest, [_sec()],
                           top=3, as_json=True))
        self.assertEqual(set(recs[0]), _STEP_KEYS)
        # descending by w2_src (the default metric).
        w2s = [r["w2_src"] for r in recs]
        self.assertEqual(w2s, sorted(w2s, reverse=True))
        self.assertEqual(recs[0]["lemma"], "m3_wide")     # the 51-token step


class SummaryJsonSchema(unittest.TestCase):
    def test_summary_json_is_per_proof_records(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_summary, [_sec()], as_json=True))
        self.assertTrue(recs)
        for r in recs:
            self.assertEqual(set(r), _SUMMARY_KEYS)
        red = next(r for r in recs if r["lemma"] == "redundant")
        self.assertEqual((red["n_goals"], red["w2_src_max"], red["w1_est_max"]),
                         (3, 11, 2))
        self.assertAlmostEqual(red["dag_ratio_est_max"], 33 / 8)
        self.assertEqual(red["ratio"], 2.0)


# -- behaviour --------------------------------------------------------------

class Widest(unittest.TestCase):
    def test_ranked_by_w2(self):
        out = _run(shape_cmds.cmd_shape_widest, [_sec()], top=2)
        # first data row names the 51-token m3_wide step.
        first = next(ln for ln in out.splitlines()
                     if ln.strip().startswith("51"))
        self.assertIn("m3_wide", first)

    def test_metric_live_reranks(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_widest, [_sec()],
                           top=3, metric="live", as_json=True))
        lives = [r["live"] for r in recs]
        self.assertEqual(lives, sorted(lives, reverse=True))


class StepsScoping(unittest.TestCase):
    def test_locus_scopes_to_lines(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                           span="Shape:60..62", as_json=True))
        self.assertEqual([r["line"] for r in recs], [60, 61, 62])

    def test_bare_theory_name_scopes_to_theory(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_steps, [_sec()],
                           span="Shape", as_json=True))
        self.assertTrue(all(r["theory"] == "Shape" for r in recs))

    def test_bad_span_exits(self):
        with self.assertRaises(SystemExit):
            _run(shape_cmds.cmd_shape_steps, [_sec()], span="NoSuchThing")


class Lemma(unittest.TestCase):
    def test_footer_reports_the_aggregate(self):
        out = _run(shape_cmds.cmd_shape_lemma, [_sec()], "redundant")
        self.assertIn("3 goals (0 bare)", out)
        self.assertIn("M6 widest block", out)      # the extension curve prints
        self.assertIn("dag:max 4.12", out)

    def test_unknown_name_is_reported_not_crashed(self):
        out = _run(shape_cmds.cmd_shape_lemma, [_sec()], "does_not_exist")
        self.assertIn("No proof-bearing entry", out)


class Census(unittest.TestCase):
    """`cmd_shape_census` takes `(name, thunk)` groups, not sections: it loads
    one session at a time so memory stays bounded and a bad session is isolated.
    A single fixture section is therefore a corpus of one group."""

    @staticmethod
    def _group(sec):
        return [("Shape", lambda: [sec])]

    def test_streams_one_record_per_proof(self):
        recs = _jsonl(_run(shape_cmds.cmd_shape_census, self._group(_sec())))
        lemmas = {r["lemma"] for r in recs}
        self.assertIn("redundant", lemmas)
        # flat_proof has a step (the `by`) but no goals — still one record.
        self.assertIn("flat_proof", lemmas)

    def test_resume_skips_done_entries(self):
        with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False,
                                         encoding="utf-8") as fh:
            fh.write(json.dumps({"theory": "Shape", "lemma": "redundant"}) + "\n")
            done_path = fh.name
        try:
            recs = _jsonl(_run(shape_cmds.cmd_shape_census,
                               self._group(_sec()), resume=done_path))
        finally:
            os.unlink(done_path)
        self.assertNotIn("redundant", {r["lemma"] for r in recs})
        self.assertIn("framing", {r["lemma"] for r in recs})   # others remain

    def test_load_done_tolerates_a_truncated_final_line(self):
        with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False,
                                         encoding="utf-8") as fh:
            fh.write(json.dumps({"theory": "T", "lemma": "a"}) + "\n")
            fh.write('{"theory": "T", "lemma": "b"')     # killed mid-write
            path = fh.name
        try:
            done = shape_cmds._load_done(path)
        finally:
            os.unlink(path)
        self.assertEqual(done, {("T", "a")})              # the good line only


if __name__ == "__main__":
    unittest.main()
