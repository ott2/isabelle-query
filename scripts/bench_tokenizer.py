#!/usr/bin/env python3
r"""CPU time of the tokenizer alone (`parsing.scan_regions`, as the parse
calls it) over a fixed set of theories.

Times only the scan, so a change to the state machine is measured apart
from the rest of a parse, and by `process_time`, so another process's load
does not count.  Prints the minimum of ``--repeat`` passes.  It imports
whichever `isabelle_query` is first on `sys.path`, so compare trees as

    PYTHONPATH=$PWD/.stage/old/src python scripts/bench_tokenizer.py
    python scripts/bench_tokenizer.py

    python scripts/bench_tokenizer.py [ROOT] [--sessions=N] [--repeat=R]

`--sessions=N` takes an ALPHABETICAL PREFIX of the sessions (default all).
`unread` is passed when this version's `scan_regions` takes it, as the
parse does.
"""

from __future__ import annotations

import inspect
import sys
import time
from pathlib import Path

import isabelle_query
from isabelle_layout import iter_sessions, session_theories
from isabelle_query import parsing


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    sessions = iter_sessions(root)
    if "--sessions" in opt:
        sessions = sessions[:int(opt["--sessions"])]
    repeat = int(opt.get("--repeat", 5))
    seen: set[Path] = set()
    texts = []
    for s in sessions:
        for _name, p in session_theories(s):
            if p not in seen and p.is_file():
                seen.add(p)
                texts.append(p.read_text(encoding="utf-8").splitlines())
    takes = "unread" in inspect.signature(parsing.scan_regions).parameters
    cpu = []
    for _ in range(repeat):
        c = time.process_time()
        for lines in texts:
            if takes:
                parsing.scan_regions(lines, want_inner=True, unread={})
            else:
                parsing.scan_regions(lines, want_inner=True)
        cpu.append(time.process_time() - c)
    print(f"{isabelle_query.__file__}: {len(texts)} theories, "
          f"{sum(map(len, texts)):,} lines, unread={takes}; cpu min "
          f"{min(cpu):.2f}s of {' '.join(f'{x:.2f}' for x in cpu)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
