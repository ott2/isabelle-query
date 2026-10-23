#!/usr/bin/env python3
"""Whole-root `summary` time with individual parse passes stubbed out.

Runs `query summary -R ROOT` in-process, once per variant per round,
alternating the order each round so drift on a busy machine hits every
variant alike.  It reports CPU time, not wall time: other processes
barely move it, while a loaded machine moved wall time by 40% between
rounds.  Compare the ratios, not the seconds.

    python scripts/probe_summary_parts.py [ROOT] [--rounds=N]

Variants: `full`; `no-mid` (`parsing._mid_decls` returns nothing,
[midline-decl]); `no-heading` (`_mark_preambles_under_headings` does
nothing, [preamble-heading]).
"""

import contextlib
import io
import sys
import time
from pathlib import Path

from isabelle_query import cli, parsing

REAL = {"_mid_decls": parsing._mid_decls,
        "_mark_preambles_under_headings":
            parsing._mark_preambles_under_headings}
VARIANTS = {
    "full": {},
    "no-mid": {"_mid_decls": lambda outer: []},
    "no-heading": {"_mark_preambles_under_headings": lambda *a: None},
}


def run(root: Path, stubs: dict) -> float:
    for name, fn in REAL.items():
        setattr(parsing, name, stubs.get(name, fn))
    saved, sys.argv = sys.argv, ["query", "summary", "-R", str(root)]
    t0 = time.process_time()
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            cli.main()
    except SystemExit:
        pass
    finally:
        sys.argv = saved
    return time.process_time() - t0


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    rounds = int(opt.get("--rounds", 2))
    names = list(VARIANTS)
    total = dict.fromkeys(names, 0.0)
    for r in range(rounds):
        for name in (names if r % 2 == 0 else names[::-1]):
            total[name] += run(root, VARIANTS[name])
    for name, fn in REAL.items():
        setattr(parsing, name, fn)
    base = total["full"]
    for name in names:
        print(f"{name:11} {total[name] / rounds:6.2f}s  "
              f"{100 * (total[name] - base) / base:+.1f}%")
    return 0


if __name__ == "__main__":
    sys.exit(main())
