#!/usr/bin/env python3
r"""What is actually IN `n_bare`, by provenance [bare-provenance].

`ProofSummary.n_bare` counts goal steps with no as-written proposition, and it
used to pool two unrelated things — *bare by construction* (`show ?thesis`,
`also`, `interpret`) and *the scanner found none*.  That pooling is what hid
issue #9(b) for as long as it did: a wrapped statement was booked as bare, where
nobody would look for a scanner fault.

This measured the population so the buckets could be named after what is in it
rather than guessed at, and now REPORTS against the shipped classifier — it
calls `shape.bare_kind` through `Step.bare` rather than keeping a second copy
of the rule, so the probe cannot agree with a classifier the tool does not use.
Each bucket prints real examples, which is what makes a shifted boundary
visible rather than merely a changed number.

    python scripts/probe_bare_provenance.py [ROOT] [--limit=N]

Whole AFP, 2026-08-31:

    883,246 goal steps, 195,733 bare (22.16%)
    construction  173,613  88.70%   `?thesis`, `?case`, `also`, `interpret`
    unfound        11,766   6.01%   `obtain x where` with the statement below
    undelimited    10,354   5.29%   `hence False by simp` — written, unquoted

Whole AFP, 2026-10-21, after #26 read a wrapped `obtain` and a label below:

    913,905 goal steps, 188,289 bare (20.60%)
    construction  178,204  94.64%
    undelimited     9,587   5.09%
    unfound           498   0.26%   `consider` / `(a) "P" | (b) "Q"`

Session-at-a-time like `shape census`, so memory stays bounded by the largest
session rather than the corpus.  `--limit=N` takes the first N sessions, which
is an ALPHABETICAL PREFIX and not a sample — fine for a shape, never for a rate.
"""

from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_layout import iter_sessions  # noqa: E402
from isabelle_query import shape  # noqa: E402
from isabelle_query.parsing import sections_for_session  # noqa: E402


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    limit = next((int(a.split("=")[1]) for a in sys.argv[1:]
                  if a.startswith("--limit=")), None)

    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    buckets: Counter[str] = Counter()
    by_cmd: Counter[str] = Counter()
    examples: dict[str, list[str]] = {}
    n_goals = n_bare = n_proofs = 0
    seen: set[Path] = set()

    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            lines = sec.source()
            for entry in sec.entries:
                try:
                    pm = shape.analyze_proof(sec, entry)
                except Exception:  # noqa: BLE001
                    continue
                if pm is None or not pm.steps:
                    continue
                n_proofs += 1
                for s in pm.goals:
                    n_goals += 1
                    if s.stmt_text:
                        continue
                    n_bare += 1
                    line = lines[s.line - 1] if s.line <= len(lines) else ""
                    buckets[s.bare] += 1
                    by_cmd[s.goal_cmd or s.kw] += 1
                    examples.setdefault(s.bare, []).append(
                        f"{sec.theory}:{s.line}  {line.strip()[:74]}")

    print(f"{n_proofs} proofs, {n_goals} goal steps, {n_bare} bare "
          f"({100 * n_bare / n_goals if n_goals else 0:.2f}% of goal steps)")
    print()
    print(f"{'bucket':16} {'count':>8} {'% of bare':>10}  examples")
    for b, n in buckets.most_common():
        print(f"{b:16} {n:8} {100 * n / n_bare:9.2f}%  {examples[b][0]}")
        for ex in examples[b][1:4]:
            print(f"{'':16} {'':8} {'':10}  {ex}")
    print()
    print("by command:", dict(by_cmd.most_common()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
