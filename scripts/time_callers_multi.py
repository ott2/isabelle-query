#!/usr/bin/env python3
"""How `callers -r` scales with the number of names in one call [issue-14].

Takes the first N named entries of THEORY and times `query -R ROOT callers -r
-c` on 1 name and on all N, so the per-name marginal cost is visible.  The
issue measured ~0.8 s per extra name; if that is the call graph being rebuilt
per name, sharing it should leave the marginal cost near the BFS alone.

Usage:  python3 scripts/time_callers_multi.py ROOT THEORY [N]
"""
from __future__ import annotations

import subprocess
import sys
import time
from pathlib import Path

from isabelle_query.api import parse_root


def run(root: Path, names: list[str]) -> tuple[float, str]:
    t0 = time.perf_counter()
    out = subprocess.run(["query", "-R", str(root), "callers", "-r", "-c",
                          *names], capture_output=True, text=True)
    return time.perf_counter() - t0, out.stdout


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    root, thy = Path(sys.argv[1]).expanduser(), sys.argv[2]
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    sec = next(s for s in parse_root(root) if s.theory == thy)
    names = [e.name for e in sec.entries if e.name != "?"][:n]
    t1, _ = run(root, names[:1])
    tn, out = run(root, names)
    print(f"1 name:   {t1:5.2f}s")
    print(f"{len(names)} names: {tn:5.2f}s   marginal "
          f"{(tn - t1) / max(1, len(names) - 1):.2f}s/name")
    print("names: ", " ".join(names))
    print("counts:", out.split())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
