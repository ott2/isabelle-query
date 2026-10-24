#!/usr/bin/env python3
"""Time the headers-only ROOT walk (`parsing._root_theories`) that a theory
resolver reads, against a full parse, for the cost note in #34.

    python scripts/time_root_theories.py ROOT [--full] [--resolve=N]

`--resolve=N` times one `api.resolve_theories` call on N theory names (the
first N the walk lists, every third spelled as a path-like label).
"""
import sys
import time
from pathlib import Path

from isabelle_query.parsing import _root_theories, _sections_from_dir

root = Path(sys.argv[1]).expanduser()
t = time.process_time()
pairs, _ = _root_theories(root)
print(f"headers-only: {len(pairs):,} theories in "
      f"{time.process_time() - t:.2f} s CPU")
if "--full" in sys.argv:
    t = time.process_time()
    secs: list = []
    _sections_from_dir(root, set(), secs)
    print(f"full parse:   {len(secs):,} sections in "
          f"{time.process_time() - t:.2f} s CPU")

opt = dict(a.split("=", 1) for a in sys.argv[2:] if "=" in a)
if "--resolve" in opt:
    from isabelle_query import api
    n = int(opt["--resolve"])
    names = [name if i % 3 else f"{path.parent.name}/{name}"
             for i, (name, path) in enumerate(pairs[:n])]
    t = time.process_time()
    got = api.resolve_theories(names, root=root)
    print(f"resolve_theories: {n} names in "
          f"{time.process_time() - t:.2f} s CPU, "
          f"{sum(len(v) == 1 for v in got.values())} unique")
