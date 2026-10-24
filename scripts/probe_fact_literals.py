#!/usr/bin/env python3
r"""What reading fact literals as citations moves in the census (#31).

Pooled over every goal step: the step count, total fan-in (M5a), goals
citing at least one fact, goals whose method coverage failed, and the
call-graph edge count (the shadowed-name path reads backquoted text now).
Run it on the new tree, then on the old one, and compare:

    python scripts/probe_fact_literals.py [ROOT] [--limit=N]
    env PYTHONPATH=.stage/old/src python scripts/probe_fact_literals.py ...

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import sys
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import graph, shape
from isabelle_query.parsing import sections_for_session


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    print(f"code: {graph.__file__}", file=sys.stderr)
    seen: set = set()
    goals = fanin = cited = uncovered = edges = 0
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
                steps = shape._scan_steps(sec, e)
                shape.annotate_fanin(steps, sec)
                for s in steps:
                    if s.kind != "goal":
                        continue
                    goals += 1
                    fanin += s.fanin
                    cited += bool(s.fanin)
                    uncovered += not s.fanin_covered
        cg = graph._build_call_graph(secs)
        edges += sum(len(v) for v in cg.callees.values())
    print(f"goal steps     {goals:,}")
    print(f"fan-in total   {fanin:,}  mean {fanin / max(goals, 1):.4f}")
    print(f"goals citing   {cited:,}")
    print(f"uncovered      {uncovered:,}")
    print(f"graph edges    {edges:,}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
