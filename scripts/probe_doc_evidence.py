#!/usr/bin/env python3
r"""Which entries carry `doc` evidence over a corpus, and what it costs.

Prints one sorted line per name with `doc` evidence (`unused`'s
`commands._evidence`), so two runs diff with `LC_ALL=C comm`.  stderr gets
the package file it ran, then the load and evidence times.  It imports
whichever `isabelle_query` is first on `sys.path`, so an old tree runs as

    git archive HEAD src | tar -x -C .stage/old
    PYTHONPATH=$PWD/.stage/old/src python scripts/probe_doc_evidence.py > old
    python scripts/probe_doc_evidence.py > new

    python scripts/probe_doc_evidence.py [ROOT] [--repeat=N]

`--repeat=N` runs the evidence pass N times after the one load and reports
each time and the minimum, which a busy machine disturbs least, as CPU time
(`process_time`) beside wall time: another process's load inflates the wall
clock, not this process's CPU time.  A cache the
pass keeps between calls (`graph._SPACE_VIS`) is cleared before each run.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

import isabelle_query
from isabelle_query import cli, commands


def main() -> int:
    print(f"# {isabelle_query.__file__}", file=sys.stderr)
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    repeat = int(opt.get("--repeat", 1))
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    cli._ROOT_OVERRIDE = root.resolve()
    t0 = time.perf_counter()
    sections = cli.load_index()
    t1 = time.perf_counter()
    times, cpu = [], []
    for _ in range(repeat):
        cache = getattr(commands._graph, "_SPACE_VIS", None)
        if cache is not None:
            cache[:] = [None] * len(cache)
        t, c = time.perf_counter(), time.process_time()
        ev = commands._evidence(sections)
        times.append(time.perf_counter() - t)
        cpu.append(time.process_time() - c)
    print(f"# {len(sections)} theories; load {t1 - t0:.1f}s; evidence "
          f"cpu min {min(cpu):.2f}s of {' '.join(f'{x:.2f}' for x in cpu)}; "
          f"wall min {min(times):.2f}s", file=sys.stderr)
    sys.stdout.writelines(sorted(f"{n}\n" for n, kinds in ev.items()
                                 if "doc" in kinds))
    return 0


if __name__ == "__main__":
    sys.exit(main())
