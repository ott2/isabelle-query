r"""Command layer for the ``query shape`` subcommand family.

Five verbs over the shape engine (``shape.py``), one view each:

* ``shape summary``            — per-theory aggregate table (``--json`` -> one
                                 per-proof :func:`shape.summary_record` per line).
* ``shape steps [SPAN]``       — the per-step table for the project or a scoped
                                 ``THEORY`` / ``THEORY:A..B`` locus (``--json`` ->
                                 one :func:`shape.step_record` per line).
* ``shape lemma NAME...``      — the full per-step view of one proof, its
                                 aggregate footer, and its M6 extension curve.
* ``shape widest [-N N]``      — the N widest steps in scope by a chosen metric
                                 (the step analogue of ``largest``).
* ``shape census``             — stream one per-proof JSONL record per entry,
                                 resumable, for a whole-AFP distribution run;
                                 one session at a time in a single process, so
                                 memory is bounded by the largest session and a
                                 session that fails to parse is skipped, not
                                 fatal.

This module only *formats*; every number comes from ``shape``.  It sits above
``commands`` in the module DAG (it reuses ``_parse_locus`` / ``_resolve_theory``
/ ``_owner_field``) and below ``cli`` (which wires the argparse tree and
re-exports these ``cmd_shape_*`` through its facade).

JSONL schema (the join contract — deliverable #2)
-------------------------------------------------
Two record shapes, keyed by the stable ``(theory, lemma)`` position — plus
``(line, col)`` for a step, since several commands may share a line — so a
value can later be joined against a per-step LLM-tractability experiment
with no re-instrumentation.  Estimator columns carry an ``_est`` suffix; exact
source metrics do not.

**Per-step record** (``shape steps --json``, ``shape lemma --json``,
``shape widest --json``) — one object per Isar command (a step), wherever
the line breaks fall:

===================  =========================================================
key                  meaning
===================  =========================================================
``theory``           theory name (position key)
``lemma``            enclosing entry name (position key)
``line``             1-indexed source line of the command (position key)
``col``              0-indexed column the command starts at (position key)
``block``            proof-block id (sibling blocks differ; M4/M6 group on it)
``depth``            proof-block nesting depth (0 = lemma's own proof body)
``kind``             ``goal`` / ``context`` / ``plumbing`` / ``closing`` / ``other``
``kw``               the command keyword (or ``.``/``..``)
``goal_cmd``         fact-binding goal command; ``""`` off goals
``method``           a ``by``/``apply`` step's method (``by simp`` -> ``simp``, ``by (rule r)`` -> ``rule``); ``""`` if none
``label``            the step's own fact label (``have key:`` -> ``key``)
``stmt_start``       1-indexed first line of the proposition span (0 if none)
``stmt_end``         1-indexed last line of the proposition span (0 if none)
``w2_src``           **M2** as-written proposition width in tokens (exact)
``w1_est``           **M1** distinct free variables (estimator)
``w1_schematic_est`` distinct schematic ``?vars`` (estimator)
``w1_bound_est``     distinct statement-local bound variables (estimator)
``fanin``            **M5a** distinct facts cited for a goal: its own, a ``from`` before it, ``using`` and methods after it
``fanin_covered``    ``false`` if a method shape could not be classified
``live``             **M5b** named facts simultaneously live at the step
``introduces``       **M5c** whether the step binds a reusable fact
``consumes``         **M5c** a goal with ``fanin`` > 0, or a step citing facts no goal took
``frame_ratio``      **M3** mentioned/max(changed,1), or ``null`` — *only under --config*
``frame_mentioned``  M3 component accesses — *only under --config*
``frame_changed``    M3 changed components — *only under --config*
===================  =========================================================

**Per-proof record** (``shape summary --json``, ``shape census``) — one object
per PROOF: every goal entry's, and every proof a command carries without
declaring a fact (``instance``, ``sublocale``, ``interpretation``,
``termination``, ``typedef``, ``notepad``, ... — ``parsing.PROOF_OWNERS``).
Fields: ``session`` (provenance: the Isabelle session the
theory was declared by, ``null`` when the load had no session context — a corpus
run needs it because 505 of 8,849 AFP theory names are used by more than one
theory, so ``(theory, lemma)`` alone cannot say which entry a record came from),
``theory``, ``lemma`` (the declared name, ``?`` for none), ``tag`` (what owns
the proof: ``LEMMA``, ``THEOREM``, ... or ``INSTANCE``, ``SUBLOCALE``, ...),
``line`` (where it starts; ``(theory, line)`` is the key, since ``?`` names
most owners and every anonymous lemma), ``n_steps`` (Isar commands, not
lines), ``n_goals``,
``n_bare``, ``depth_max`` (Length: max proof-block nesting, 1 = flat),
``w2_src_max``/``_mean``/``_p90``, ``w1_est_max``/``_mean``,
``fanin_max``/``_mean`` (**M5a** explicit source-cited premises per goal step),
``fanin_cited`` (goal steps citing ≥1 — the denominator of the *conditional*
fan-in, the mean over citing steps only), ``live_max``/``_mean``,
``dag_ratio_est_max`` (**M4**),
``introduce``, ``consume``, ``both`` (**M5c** steps that introduce, cite, and
do both — a citation counted once, on the goal it serves — so the three-way
split is ``introduce - both`` / ``consume - both`` / ``both``),
``ratio`` (``null`` when nothing consumed),
``trivial_frac`` (fraction of discharged steps closed by ``simp``/``auto``/…;
``null`` when nothing is discharged by a recognised method),
``removable_w2_est_at_8`` (**M6** fraction of stated width removable by naming
≤8 repeated chunks per block), ``method_kinds`` (the *automation axis*
profile: a histogram of discharged steps by method kind — ``automation`` /
``search`` / ``arith`` / ``structural`` / ``other`` — a finer grain than
``trivial_frac`` over the same discharged-step denominator), ``methods`` (how
each method is applied, ``position:name/modifier`` -> count: ``by:simp/only``,
``apply:rule``, ``proof:induct/arbitrary``, ``qed:simp``, ``proof:-``,
``.``, ``..`` — over every command, and ``method_kinds`` is its ``by:`` /
``apply:`` forms bucketed by name), and ``bare_kinds``
(why each of the ``n_bare`` steps states no proposition — ``construction`` /
``undelimited`` / ``unfound``, summing to ``n_bare``, which is unchanged).
Those three are the nested fields.
This record is designed to be a *sufficient statistic* per proof — the analysis
layer reads these scalars, never re-scans.
"""

from __future__ import annotations

import json
import sys
from collections.abc import Callable, Iterable
from typing import NamedTuple

from isabelle_query import shape
from isabelle_query._corpus_constants import CORPUS_CONSTANTS
from isabelle_query._prog import prog_name
from isabelle_query.commands import (
    _owner_field,
    _parse_locus,
    _resolve_theory,
)
from isabelle_query.model import Entry, TheorySection
from isabelle_query.render import locus_labels
from isabelle_query.shape import CorpusConfig


# -- shared helpers ---------------------------------------------------------

# Metric extractors for the ranked / tabular views, keyed by the `--metric`
# name.  Each takes a Step and its classifier context (w1 needs the context;
# the others ignore it), so one dict serves `widest` and the `steps` table.
_METRICS = {
    "w2": lambda s, ctx: shape.w2_src(s),
    "w1": lambda s, ctx: shape.w1_est(s, ctx).free,
    "fanin": lambda s, ctx: s.fanin,
    "live": lambda s, ctx: s.live,
}


def _preview(text: str, cap: int = 56) -> str:
    """A one-line, length-capped statement preview for the human tables."""
    text = " ".join(text.split())
    return text if len(text) <= cap else text[:cap - 1] + "…"


def _resolve_span(sections: list[TheorySection], span: str | None
                  ) -> tuple[str | None, int | None, int | None]:
    """Resolve a ``steps`` SPAN token to ``(theory, lo, hi)`` line bounds.

    Two forms, the same grammar ``enclosing`` / ``lines`` use: a ``THEORY:A..B``
    (or ``THEORY:LINE``) locus, or a bare ``THEORY`` name (whole theory).  An
    open ``THEORY:A..`` resolves ``hi`` to the theory end.  Returns
    ``(None, None, None)`` for no span (the whole project).  Exits on an
    unresolvable token, matching the FILES resolver's fail-fast.
    """
    if not span:
        return None, None, None
    locus = _parse_locus(span)
    if locus is not None:
        file_token, lo, hi = locus
        sec = _resolve_theory(sections, file_token)
        theory = sec.theory if sec is not None else file_token
        if hi is None:                       # open `A..` -> to theory end
            hi = sec.thy_lines if sec is not None else 10 ** 9
        return theory, lo, hi
    sec = _resolve_theory(sections, span)
    if sec is None:
        print(f"ERROR: not a theory or FILE:A..B locus: {span}", file=sys.stderr)
        sys.exit(1)
    return sec.theory, None, None


def _resolve_lemma(sections: list[TheorySection], name: str
                   ) -> tuple[TheorySection, Entry] | None:
    """Find the ``(section, entry)`` for a lemma NAME — exact match first, then
    unique-ish substring (matching ``show``'s exact-then-substring lookup)."""
    for sec in sections:
        for e in sec.entries + sec.proof_owners:
            if e.name == name:
                return sec, e
    for sec in sections:
        for e in sec.entries + sec.proof_owners:
            if e.name != "?" and name in e.name:
                return sec, e
    return None


# -- summary ----------------------------------------------------------------

def _proof_size(pm, ps: shape.ProofSummary, scope: str, content: str) -> int:
    """The size (in lines) of one proof under the ``--scope`` / ``--content``
    selection.  Proof scope reuses the cached ``ProofSummary`` counts; entry
    scope recomputes over the whole-entry span (statement + proof + doc)."""
    if scope == "proof":
        raw, code = ps.proof_lines, ps.proof_lines_code
    else:  # entry
        raw, code, _, _ = shape._region_counts(
            pm.sec, pm.entry.src_start, pm.entry.thy_end)
    if content == "code":
        return code
    if content == "prose":
        return raw - code
    return raw


def cmd_shape_summary(sections: list[TheorySection], as_json: bool = False,
                      corpus_consts: frozenset[str] = CORPUS_CONSTANTS,
                      scope: str = "proof", content: str = "all") -> None:
    """Per-theory shape aggregate table (default), or one per-proof JSONL record
    per line (``--json``).  Table columns are *maxes* — the widest single
    occurrence in each theory — plus counts; per-proof means live in the JSONL,
    which downstream re-aggregates however it needs.  The ``lines:max`` column is
    the largest proof (or ``--scope entry``) in ``--content`` lines."""
    pairs = [(pm, shape.summarize(pm))
             for pm in shape.analyze_sections(sections, corpus_consts)]
    if as_json:
        for _pm, ps in pairs:
            print(json.dumps(shape.summary_record(ps)))
        return
    if not pairs:
        print("No proofs with structured steps found.")
        return

    by_theory: dict[str, list[tuple[shape.ProofSummary, int]]] = {}
    for pm, ps in pairs:
        by_theory.setdefault(ps.theory, []).append(
            (ps, _proof_size(pm, ps, scope, content)))

    print("# Proof shape summary\n")
    print(f"{len(pairs)} proofs across {len(by_theory)} theories  "
          f"(source-level shape metrics, parsed live)\n")
    print("Per-theory maxes: the widest single step, most-cited step, peak live "
          "facts,\nwidest block (M4 DAG ratio), and the longest "
          f"{scope} in {content} lines.  `--json` emits one per-proof record "
          "for real analysis.\n")
    hdr = ("| Theory | Proofs | Goals | depth:max | Bare% | w2:max | w1:max | "
           "fanin:max | live:max | dag:max | lines:max |")
    print(hdr)
    print("|--------|-------:|------:|----------:|------:|-------:|-------:|"
          "----------:|---------:|--------:|----------:|")
    for theory, rows in by_theory.items():
        print(_summary_row(theory, rows))
    if len(by_theory) > 1:
        print(_summary_row("**TOTAL**",
                           [pair for rows in by_theory.values() for pair in rows]))


def _summary_row(label: str, rows: list[tuple[shape.ProofSummary, int]]) -> str:
    """One aggregate table row over ``(summary, size)`` rows — counts summed,
    metrics (including the selected ``lines`` size) maxed."""
    pss = [ps for ps, _sz in rows]
    goals = sum(r.n_goals for r in pss)
    bare = sum(r.n_bare for r in pss)
    bare_pct = (100.0 * bare / goals) if goals else 0.0
    return (f"| {label} | {len(pss)} | {goals} | "
            f"{max(r.depth_max for r in pss)} | {bare_pct:.0f}% | "
            f"{max(r.w2_max for r in pss)} | {max(r.w1_max for r in pss)} | "
            f"{max(r.fanin_max for r in pss)} | "
            f"{max(r.live_max for r in pss)} | "
            f"{max(r.dag_max for r in pss):.2f} | "
            f"{max(sz for _ps, sz in rows)} |")


# -- steps ------------------------------------------------------------------

def cmd_shape_steps(sections: list[TheorySection], span: str | None = None,
                    as_json: bool = False, all_steps: bool = False,
                    cfg: CorpusConfig | None = None,
                    corpus_consts: frozenset[str] = CORPUS_CONSTANTS) -> None:
    """Per-step shape records, optionally scoped to a ``THEORY`` / ``THEORY:A..B``
    SPAN.  The human table shows goal steps (``-a`` adds structural steps);
    ``--json`` streams one :func:`shape.step_record` per emitted step.  A corpus
    ``cfg`` adds the M3 ``frame_*`` columns to the JSON."""
    theory, lo, hi = _resolve_span(sections, span)
    # The label, not `step.theory`: a `Step` carries a theory NAME, which is
    # the JSON record's position key and must stay one, but the human table
    # prints a locus and 461 AFP theory names are shared [disambig-loci].
    labels = locus_labels(sections)
    rows = []  # (step, ctx, lines, label)
    for pm in shape.analyze_sections(sections, corpus_consts):
        if theory is not None and pm.theory != theory:
            continue
        lines = pm.sec.source()
        label = labels.get(pm.sec.path, pm.theory)
        for s in pm.steps:
            if lo is not None and not (lo <= s.line <= hi):
                continue
            if not all_steps and s.kind != "goal":
                continue
            rows.append((s, pm.ctx, lines, label))

    if as_json:
        for s, ctx, lines, _label in rows:
            print(json.dumps(shape.step_record(s, ctx, lines, cfg)))
        return
    if not rows:
        print("No steps in scope.")
        return
    print(f"{'location':<20} {'kind':<8} {'w2':>4} {'w1':>4} {'fan':>4} "
          f"{'live':>4}  statement")
    print(f"{'-' * 20:<20} {'-' * 8:<8} {'-' * 4:>4} {'-' * 4:>4} {'-' * 4:>4} "
          f"{'-' * 4:>4}  {'-' * 9}")
    for s, ctx, _lines, label in rows:
        print(_step_row(s, ctx, label))


def _step_row(step: shape.Step, ctx: shape.ClassifyCtx, label: str) -> str:
    """One aligned per-step table row (location, kind, the four metrics, and a
    statement preview).  ``label`` is the theory's `locus_labels` name."""
    loc = f"{label}:{step.line}"
    w1 = shape.w1_est(step, ctx).free
    return (f"{loc:<20} {step.kind:<8} {shape.w2_src(step):>4} {w1:>4} "
            f"{step.fanin:>4} {step.live:>4}  {_preview(step.stmt_text)}")


# -- lemma ------------------------------------------------------------------

def cmd_shape_lemma(sections: list[TheorySection], name: str,
                    as_json: bool = False, cfg: CorpusConfig | None = None,
                    corpus_consts: frozenset[str] = CORPUS_CONSTANTS) -> None:
    """The full shape view of one proof: its per-step table, aggregate footer,
    and M6 extension curve for the widest block.  ``--json`` emits one
    :func:`shape.step_record` per step of the lemma (all kinds)."""
    found = _resolve_lemma(sections, name)
    if found is None:
        print(f"No proof-bearing entry matching '{name}'.")
        return
    sec, entry = found
    pm = shape.analyze_proof(sec, entry, corpus_consts)
    if pm is None:
        print(f"'{entry.name}' has no structured proof body.")
        return
    lines = sec.source()

    if as_json:
        for s in pm.steps:
            print(json.dumps(shape.step_record(s, pm.ctx, lines, cfg)))
        return

    ps = shape.summarize(pm)
    thy = locus_labels(sections).get(sec.path, sec.theory)
    print(f"{entry.name}  ({entry.tag} {thy}:{entry.src_start}.."
          f"{entry.thy_end})\n")
    print(f"{'line':>5} {'kind':<8} {'w2':>4} {'w1':>4} {'fan':>4} {'live':>4}"
          f"  statement")
    for s in pm.steps:
        w1 = shape.w1_est(s, pm.ctx).free
        print(f"{s.line:>5} {s.kind:<8} {shape.w2_src(s):>4} {w1:>4} "
              f"{s.fanin:>4} {s.live:>4}  {_preview(s.stmt_text)}")
    print(f"\n{ps.n_goals} goals ({ps.n_bare} bare)  "
          f"w2 max {ps.w2_max} mean {ps.w2_mean:.1f}  "
          f"w1 max {ps.w1_max}  fan-in max {ps.fanin_max}  "
          f"live max {ps.live_max} mean {ps.live_mean:.1f}")
    ratio = "n/a" if ps.ratio is None else f"{ps.ratio:.2f}"
    print(f"M4 dag:max {ps.dag_max:.2f}   "
          f"M5c introduce/consume {ps.intro}/{ps.consume} (ratio {ratio})")
    _print_m6(pm)


def _print_m6(pm: shape.ProofMetrics) -> None:
    """Print the M6 width-vs-k curve for the proof's widest block (the block with
    the largest raw summed w2), or nothing when no block has goal statements."""
    curves = shape.extension_curve(pm.steps, pm.ctx)
    curves = [c for c in curves if c.w2 and c.w2[0] > 0]
    if not curves:
        return
    c = max(curves, key=lambda c: c.w2[0])
    ks = "  ".join(f"{k:>4}" for k in c.ks)
    w2 = "  ".join(f"{v:>4}" for v in c.w2)
    print(f"M6 widest block ({c.n_goals} goals)  k: {ks}")
    print(f"{'':>26}w2: {w2}")


# -- widest -----------------------------------------------------------------

def cmd_shape_widest(sections: list[TheorySection], top: int = 20,
                     metric: str = "w2", as_json: bool = False,
                     corpus_consts: frozenset[str] = CORPUS_CONSTANTS) -> None:
    """The N widest goal steps in scope, ranked by ``metric`` (``w2`` default,
    or ``w1`` / ``fanin`` / ``live``) — the step analogue of ``largest``.  Ties
    break by source position for determinism.  ``--json`` emits the ranked
    :func:`shape.step_record`s."""
    key = _METRICS[metric]
    labels = locus_labels(sections)
    rows = []  # (value, theory, line, step, ctx, lines, label)
    for pm in shape.analyze_sections(sections, corpus_consts):
        lines = pm.sec.source()
        label = labels.get(pm.sec.path, pm.theory)
        for s in pm.goals:
            rows.append((key(s, pm.ctx), s.theory, s.line, s, pm.ctx, lines,
                         label))
    # widest first; ties by (theory, line) ascending for a stable order.  The
    # sort key stays the theory NAME, not the label: the tie-break is about
    # determinism, and a qualified label would reorder equal-width rows for no
    # reason a reader could see.
    rows.sort(key=lambda r: (-r[0], r[1], r[2]))
    rows = rows[:top]

    if as_json:
        for _v, _t, _ln, s, ctx, lines, _lb in rows:
            print(json.dumps(shape.step_record(s, ctx, lines)))
        return
    if not rows:
        print("No goal steps found.")
        return
    print(f"Top {len(rows)} widest steps by {metric}:\n")
    print(f"{metric:>5} {'location':<22} {'lemma':<24}  statement")
    print(f"{'-' * 5:>5} {'-' * 22:<22} {'-' * 24:<24}  {'-' * 9}")
    for value, _theory, line, s, _ctx, _lines, label in rows:
        loc = f"{label}:{line}"
        print(f"{value:>5} {loc:<22} {s.lemma:<24}  {_preview(s.stmt_text)}")


# -- census -----------------------------------------------------------------

class CensusOutcome(NamedTuple):
    """What a census actually managed to do.  Returned rather than exited on,
    because the exit code is ``cli``'s to choose (it owns ``_EXIT_BAD_ROOT``
    and the #7 contract)."""
    sessions: int    # session groups offered
    loaded: int      # groups that parsed without raising
    skipped: int     # groups that raised (and were reported on stderr)
    records: int     # records emitted


def cmd_shape_census(
        groups: "Iterable[tuple[str, Callable[[], list[TheorySection]]]]",
        resume: str | None = None,
        corpus_consts: frozenset[str] = CORPUS_CONSTANTS) -> CensusOutcome:
    """Stream one per-proof JSONL record per entry — the whole-AFP distribution
    run — one **session** at a time, in a single process.

    ``groups`` yields ``(session_name, load)`` pairs where ``load`` is a
    *thunk* — deliberately not a ready-made section list.  Three things follow
    from that, and none is available if the caller hands over parsed sections:

    * **Memory stays bounded by the largest single session.**  Each session's
      sections are built inside the loop and dropped at the end of it.
      Measured against loading the corpus at once, the analysis is the same
      work to within 0.03s, but peak memory is flat at 29 MB (the largest AFP
      session) where the whole-corpus load grows linearly — 86 MB over 40 AFP
      entries, 315 MB over 160, gigabytes over all ~9,600 theories.
    * **A session that cannot be parsed is isolated.**  The thunk is called
      inside the ``try``, so a failure to *load* is caught alongside a failure
      to *analyse*.  One unparseable session must not lose the other 991.
    * **Startup is paid once.**  A shell loop over entries pays interpreter and
      process startup per entry, which dominates: 28.1s against 5.5s over 40
      AFP entries, for byte-identical output.

    A corpus with no sessions at all (a bare directory of ``.thy`` files) is
    simply a corpus of one unnamed group — this takes whatever grouping the
    caller supplies and does not itself know about roots.

    ``--resume FILE`` reads an existing run's ``(theory, lemma)`` keys and skips
    them, so ``census -R AFP/thys --resume out.jsonl >> out.jsonl`` picks up
    where a previous run stopped.  Config-free by design (the M3 frame ratio
    needs a per-corpus config; run ``steps --config`` where one exists).

    Skips are reported on stderr (never stdout — stdout is the JSONL stream and
    must stay machine-readable), and counted.  The caller decides what a run of
    nothing means; see :class:`CensusOutcome`.
    """
    done = _load_done(resume) if resume else set()
    sessions = loaded = skipped = records = 0
    for name, load in groups:
        sessions += 1
        try:
            sections = load()
            for pm in shape.analyze_sections(sections, corpus_consts):
                if (pm.theory, pm.lemma) in done:
                    continue
                rec = shape.summary_record(shape.summarize(pm))
                sys.stdout.write(json.dumps(rec) + "\n")
                records += 1
            # Flush per session, not per record: a killed run still leaves a
            # valid JSONL prefix, but a whole-AFP run does not pay a syscall
            # per proof.
            sys.stdout.flush()
            loaded += 1
        except BrokenPipeError:
            # NOT a session failure — the consumer went away.  `census
            # | head` is the ordinary way to eyeball a corpus run,
            # and swallowing this reported every remaining session as "skipped"
            # and then exited 2 for a run that had worked perfectly.  Let it
            # reach `main`, which ends the stream the way a Unix filter should.
            raise
        except Exception as exc:  # noqa: BLE001
            # Broad on purpose.  A census exists to survive a corpus, and the
            # failures are open-ended (unreadable file, decoding error, a
            # scanner tripping on one pathological theory).  Narrowing this
            # would trade a named exception for losing every later session.
            skipped += 1
            print(f"{prog_name()}: session {name!r} skipped: "
                  f"{type(exc).__name__}: {exc}", file=sys.stderr)
        finally:
            sections = None  # noqa: F841 — drop the session before the next
    return CensusOutcome(sessions, loaded, skipped, records)


def _load_done(path: str) -> set[tuple[str, str]]:
    """The ``(theory, lemma)`` keys already present in a prior census JSONL, for
    ``--resume``.  A missing / unreadable file is an empty set (start fresh); a
    malformed line is skipped, so a truncated final record from a kill is
    tolerated."""
    done: set[tuple[str, str]] = set()
    try:
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except ValueError:
                    continue
                if "theory" in obj and "lemma" in obj:
                    done.add((obj["theory"], obj["lemma"]))
    except OSError:
        pass
    return done
