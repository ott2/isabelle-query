#!/usr/bin/env python3
r"""How many `obtain` goal steps bind a label `Step.label` misses [obtain-label].

`_STEP_LABEL_RE` reads `CMD NAME:`, which fits `have key:` but not
`obtain x where key:`, where the label follows `where`.  An unread label is
an unnamed fact to M5b, so it never counts as live.  Counts the AFP's
`obtain` steps, those whose command text has `where LABEL:`, and how many
of those `Step.label` caught.

    python scripts/probe_obtain_labels.py [ROOT] [--limit=N]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_layout import iter_sessions  # noqa: E402
from isabelle_query import shape  # noqa: E402
from isabelle_query.parsing import sections_for_session  # noqa: E402

_WHERE_LABEL_RE = re.compile(r"\bwhere\s+[A-Za-z][\w'.]*\s*(?:\[[^\]]*\])?\s*:(?!:)")


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    limit = next((int(a.split("=")[1]) for a in sys.argv[1:]
                  if a.startswith("--limit=")), None)
    sessions = iter_sessions(root)[:limit] if limit else iter_sessions(root)
    n_obtain = n_labelled = n_caught = n_goals = n_named = 0
    seen: set = set()
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception:  # noqa: BLE001
            continue
        for sec in secs:
            for e in sec.entries:
                for s in shape._scan_steps(sec, e):
                    if s.kind != "goal":
                        continue
                    n_goals += 1
                    n_named += bool(s.label)
                    if s.goal_cmd != "obtain":
                        continue
                    n_obtain += 1
                    if _WHERE_LABEL_RE.search(s.src):
                        n_labelled += 1
                        n_caught += bool(s.label)
    print(f"{n_goals:,} goal steps, {n_named:,} with a label read")
    print(f"{n_obtain:,} obtain steps; {n_labelled:,} with `where LABEL:` on "
          f"the command's own line; {n_caught:,} of those read")
    return 0


if __name__ == "__main__":
    sys.exit(main())
