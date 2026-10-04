#!/usr/bin/env python3
"""Which sessions re-dump the method table on every warm call?

`resolve_namespace` writes its cache only when a dump returns a table, so a
session whose dump comes back EMPTY is dumped again on the next call, and the
next — an Isabelle subprocess per invocation, forever.  Replays what
`cli._configure_namespace` does for ROOT, session by session, and reports each
built session's source, time and whether a fingerprint-valid cache exists.

Usage:  python3 scripts/probe_namespace_misses.py ROOT
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

from isabelle_layout import iter_sessions

from isabelle_query import _namespace_resolve as ns


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    root = Path(sys.argv[1]).expanduser()
    infos = list(iter_sessions(root))
    dirs = sorted({str(s.root_path.parent) for s in infos})
    built = ns._built_sessions(ns._version_id(ns._isabelle_bin()))
    for s in infos:
        if s.name not in built:
            print(f"  {s.name:40} not built (skipped)")
            continue
        fp = ns.isabelle_fingerprint(s.name)
        cached = ns.load_cache(s.name)
        hit = bool(fp and cached and cached.get("fingerprint") == fp)
        t0 = time.perf_counter()
        r = ns.resolve_namespace(s.name, dirs=dirs)
        dt = time.perf_counter() - t0
        print(f"  {s.name:40} {r['source']:10} {dt:5.2f}s  "
              f"cache {'hit' if hit else 'MISS'}  parent={s.parent}")
        if r["source"] == "committed":
            # Why the dump came back empty: the process's own account.
            _m, _a, _t, proc = ns.dump(s.name, dirs=dirs)
            if proc is None:
                print("      dump: timed out or could not start")
            else:
                tail = (proc.stderr or proc.stdout).strip().splitlines()[-3:]
                print(f"      dump: exit {proc.returncode}")
                for ln in tail:
                    print(f"        {ln}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
