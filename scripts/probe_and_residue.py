#!/usr/bin/env python3
r"""What a step still gains when every `and` is removed from it (#36).

The issue's measure: rewrite each step's command text without `and` and
count the facts `graph._cited_facts_on_line` gains.  Run after the fix, it
shows what the `and` reading still misses; samples print up to `--show`.

    python scripts/probe_and_residue.py [ROOT] [--limit=N] [--show=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import graph, shape
from isabelle_query.parsing import sections_for_session

# The keyword alone: not the `and` of `\<and>`, which would change a
# literal's key and read as a gain.
_AND = re.compile(r"(?<![\\<\w])and(?![\w>])")


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 30))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    gained = lines = shown = 0
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
                    if s.kind == "other" or not s.src or "and" not in s.src:
                        continue
                    f0 = graph._cited_facts_on_line(s.src)[0]
                    f1 = graph._cited_facts_on_line(_AND.sub(" ", s.src))[0]
                    extra = f1 - f0
                    if extra:
                        gained += len(extra)
                        lines += 1
                        if shown < show:
                            shown += 1
                            print(f"{sec.path.name}:{s.line}  "
                                  f"+{sorted(extra)}  {s.src.strip()[:100]}")
    print(f"\nstill gained without `and`: {gained:,} facts on {lines:,} steps")
    return 0


if __name__ == "__main__":
    sys.exit(main())
