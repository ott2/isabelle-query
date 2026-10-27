#!/usr/bin/env python3
r"""Step lines whose fact walk changed when symbolic names became names (#35).

Loads a second copy of `graph.py` (the old fact walk, e.g. from
`git archive HEAD src | tar -x -C .stage/old`) beside the installed one,
reads every step's command text with both, and reports:

  * the facts gained and lost, pooled by kind (symbolic, quoted, other);
  * every line whose method coverage changed, up to `--show`;
  * every line that gained a fact, up to `--gains` (default none).

    python scripts/probe_symbolic_coverage.py OLD_GRAPH_PY [ROOT]
        [--limit=N] [--show=N] [--gains=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from collections import Counter
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import graph, shape
from isabelle_query.parsing import sections_for_session

_SYMBOLIC = re.compile(r"[!#$%&*+\-/<=>?@^|~][!#$%&*+\-/<=>?@^_|~]*\Z")


def _load(path: str):
    spec = importlib.util.spec_from_file_location("old_graph", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _kind(fact: str, line: str) -> str:
    if _SYMBOLIC.match(fact):
        return "symbolic"
    if f'"{fact}"' in line:
        return "quoted"
    return "other"


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    old = _load(argv[0])
    root = Path(argv[1]).expanduser() if len(argv) > 1 else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 40))
    gains = int(opt.get("--gains", 0))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    gained: Counter[str] = Counter()
    lost: Counter[str] = Counter()
    cov: Counter[str] = Counter()
    shown = gain_shown = 0
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            for e in sec.entries:
                if not e.proof_line:
                    continue
                for s in shape._scan_steps(sec, e):
                    if s.kind == "other" or not s.src:
                        continue
                    f0, c0 = old._cited_facts_on_line(s.src)
                    f1, c1 = graph._cited_facts_on_line(s.src)
                    for f in f1 - f0:
                        gained[_kind(f, s.src)] += 1
                    if f1 - f0 and gain_shown < gains:
                        gain_shown += 1
                        print(f"+{sorted(f1 - f0)} {sec.path.name}:{s.line}"
                              f"  {s.src.strip()[:110]}")
                    for f in f0 - f1:
                        lost[_kind(f, s.src)] += 1
                    if c0 != c1:
                        cov["lost" if c0 else "gained"] += 1
                        if shown < show:
                            shown += 1
                            print(f"{'-' if c0 else '+'}cov "
                                  f"{sec.path.name}:{s.line}  "
                                  f"{s.src.strip()[:110]}")
    print(f"\nfacts gained: {dict(gained)}")
    print(f"facts lost:   {dict(lost)}")
    print(f"coverage:     {dict(cov)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
