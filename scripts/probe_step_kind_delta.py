#!/usr/bin/env python3
r"""Corpus probe: what does a change to the STEP CLASSIFIER move?

`[markup-step-model]` found that a standalone `unfolding` line is not booked as
a step (5,600 of the 5,693 classifier misses Isabelle's `PIDE/markup` reports).
The fix is one word in a keyword set, and one word in a keyword set is exactly
the kind of change whose blast radius has to be measured rather than argued:
`_classify_step_line` decides `Step.kind`, and `annotate_fanin` treats
`plumbing` as an accumulator and `closing` as a flush boundary, so a keyword
that moves families moves M5a as well as the step count.

Dumps one stable-keyed record per proof so two trees can be diffed:

    python scripts/probe_step_kind_delta.py 40 > .scratch-shape-before.jsonl
    <apply the change>
    python scripts/probe_step_kind_delta.py 40 > .scratch-shape-after.jsonl
    python scripts/probe_step_kind_delta.py --diff .scratch-shape-{before,after}.jsonl

The key is `theory/line`, NOT the fact name: `?` is not unique within a theory
and a name-keyed diff silently collapses every anonymous lemma into one record.

Usage:
    probe_step_kind_delta.py [N_ENTRIES]      # dump JSONL to stdout
    probe_step_kind_delta.py --diff A B       # compare two dumps
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

AFP = Path.home() / "repos" / "afp" / "thys"

# Fields worth diffing: the step population, the kind mix, and every axis
# `annotate_fanin` or the kind field can reach.
FIELDS = ("n_steps", "n_goals", "n_bare", "fanin_max", "fanin_sum",
          "fanin_cited", "live_max", "depth_max", "trivial", "kinds")


def dump(limit: int) -> None:
    from isabelle_query import cli, shape

    for ent in sorted(d for d in AFP.iterdir() if d.is_dir())[:limit]:
        for thy_path in sorted(ent.rglob("*.thy")):
            try:
                sec = cli._parse_one(thy_path.stem, thy_path)
            except Exception:  # noqa: BLE001
                continue
            for e in sec.entries:
                try:
                    pm = shape.analyze_proof(sec, e)
                except Exception:  # noqa: BLE001
                    continue
                if pm is None:
                    continue
                steps = pm.steps
                goals = [s for s in steps if s.kind == "goal"]
                rec = {
                    "key": f"{ent.name}/{sec.theory}:{e.thy_line}",
                    "n_steps": len(steps),
                    "n_goals": len(goals),
                    "n_bare": sum(1 for s in goals if s.bare),
                    "fanin_max": max((s.fanin for s in goals), default=0),
                    "fanin_sum": sum(s.fanin for s in goals),
                    "fanin_cited": sum(1 for s in goals if s.fanin),
                    "live_max": pm.live_max,
                    "depth_max": max((s.depth for s in steps), default=0),
                    "trivial": shape.trivial_frac(steps),
                    "kinds": dict(Counter(s.kind for s in steps)),
                }
                print(json.dumps(rec))


def load(path: str) -> dict[str, dict]:
    out: dict[str, dict] = {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                r = json.loads(line)
                out[r["key"]] = r
    return out


def totals(a_path: str, b_path: str) -> None:
    """Census totals over EVERY record, not just the shared ones.

    `diff` reports the shared set, which is the right denominator for "what
    moved under a stable key" — but a change that ADDS proofs puts their steps
    outside it, so a pure redistribution and a real gain read the same there.
    This is the other half: the published totals, which is what a release note
    quotes.
    """
    a, b = load(a_path), load(b_path)
    print(f"{'field':<14}{'before':>16}{'after':>16}{'delta':>14}")
    for f in FIELDS:
        if f == "kinds":
            continue
        sa = sum(r[f] for r in a.values() if isinstance(r[f], (int, float)))
        sb = sum(r[f] for r in b.values() if isinstance(r[f], (int, float)))
        pct = f"{(sb - sa) / sa:+.2%}" if sa else "—"
        print(f"{f:<14}{sa:>16,.0f}{sb:>16,.0f}{pct:>14}")
    print(f"{'n_proofs':<14}{len(a):>16,}{len(b):>16,}"
          f"{(len(b) - len(a)) / len(a):>+14.2%}")


def diff(a_path: str, b_path: str) -> None:
    a, b = load(a_path), load(b_path)
    print(f"before {len(a):,} proofs, after {len(b):,} proofs")
    only_a = set(a) - set(b)
    only_b = set(b) - set(a)
    print(f"  proofs only before {len(only_a):,}, only after {len(only_b):,}")

    shared = sorted(set(a) & set(b))
    moved = Counter()
    totals_a, totals_b = Counter(), Counter()
    samples: dict[str, list[str]] = {}
    for k in shared:
        ra, rb = a[k], b[k]
        for f in FIELDS:
            if f == "kinds":
                for kind in set(ra["kinds"]) | set(rb["kinds"]):
                    totals_a[f"kind:{kind}"] += ra["kinds"].get(kind, 0)
                    totals_b[f"kind:{kind}"] += rb["kinds"].get(kind, 0)
                continue
            va, vb = ra[f], rb[f]
            if isinstance(va, (int, float)) and isinstance(vb, (int, float)):
                totals_a[f] += va
                totals_b[f] += vb
            if va != vb:
                moved[f] += 1
                samples.setdefault(f, []).append(
                    f"{k}  {f}: {va} -> {vb}")

    print(f"\n  {len(shared):,} proofs in both; records that MOVED, per field:")
    for f in FIELDS:
        if f == "kinds":
            continue
        n = moved[f]
        da, db = totals_a[f], totals_b[f]
        delta = f"{da:,} -> {db:,}" if da != db else f"{da:,} (unchanged)"
        print(f"    {f:<14} {n:>7,} proofs   total {delta}")
    print("\n  step-kind totals:")
    for key in sorted(set(totals_a) | set(totals_b)):
        if not key.startswith("kind:"):
            continue
        da, db = totals_a[key], totals_b[key]
        flag = "" if da == db else f"   ({db - da:+,})"
        print(f"    {key[5:]:<12} {da:>8,} -> {db:>8,}{flag}")
    for f, rows in samples.items():
        print(f"\n  first {f} moves (of {len(rows):,}):")
        for r in rows[:6]:
            print(f"    {r}")


def main() -> None:
    if sys.argv[1:2] == ["--totals"]:
        totals(sys.argv[2], sys.argv[3])
        return
    if sys.argv[1:2] == ["--diff"]:
        diff(sys.argv[2], sys.argv[3])
        return
    dump(int(sys.argv[1]) if len(sys.argv) > 1 else 40)


if __name__ == "__main__":
    main()
