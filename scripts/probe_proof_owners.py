#!/usr/bin/env python3
r"""The proofs `shape` measures that are not proofs of facts [proof-owners].

Per owning command: how many owners, how many have a proof the census now
measures, their steps and proof lines, against the same totals over goal
entries.  `todo.md`'s estimate was 16,778 commands owning 58,516 proof lines,
1.58% of all proof text (`probe_unscanned_exposure.py`, a coarser unit).

    python scripts/probe_proof_owners.py [ROOT] [--limit=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
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
    sessions = iter_sessions(root)[:limit] if limit else iter_sessions(root)
    n: Counter[str] = Counter()
    steps: Counter[str] = Counter()
    plines: Counter[str] = Counter()
    seen: set = set()
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception:  # noqa: BLE001
            continue
        for sec in secs:
            for e in sec.entries + sec.proof_owners:
                pm = shape.analyze_proof(sec, e)
                if pm is None:
                    continue
                ps = shape.summarize(pm)
                key = e.tag if e in sec.proof_owners else "(entries)"
                n[key] += 1
                steps[key] += ps.n_steps
                plines[key] += ps.proof_lines_code
    ent = "(entries)"
    own = [k for k in n if k != ent]
    o_n, o_s, o_l = (sum(c[k] for k in own) for c in (n, steps, plines))
    print(f"{'owner':<22} {'proofs':>8} {'steps':>10} {'code lines':>11}")
    for k in sorted(own, key=lambda k: -plines[k]):
        print(f"{k:<22} {n[k]:>8,} {steps[k]:>10,} {plines[k]:>11,}")
    print(f"{'all owners':<22} {o_n:>8,} {o_s:>10,} {o_l:>11,}")
    print(f"{'goal entries':<22} {n[ent]:>8,} {steps[ent]:>10,} "
          f"{plines[ent]:>11,}")
    tot_l = o_l + plines[ent]
    print(f"\nowners: {100 * o_n / (o_n + n[ent]):.2f}% of proofs, "
          f"{100 * o_s / (o_s + steps[ent]):.2f}% of steps, "
          f"{100 * o_l / tot_l:.2f}% of proof code lines")
    return 0


if __name__ == "__main__":
    sys.exit(main())
