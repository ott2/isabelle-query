#!/usr/bin/env python3
r"""Which wrapped statements `_statement_wrapped` reads, by form [bare-wrapped].

The precision half of `probe_unfound_residue.py`: that one counts what is
still missed, this one samples what is now READ, grouped by what stands
between the command line and the delimiter on the next line -- nothing,
`where`, a label, or both -- so a form that invents statements shows up as
a bad example rather than as a smaller `unfound`.

    python scripts/probe_wrapped_reads.py [ROOT] [--limit=N] [--per=N] [--seed=N]

`--per` examples per form, sampled uniformly (seeded) from the whole corpus.
"""

from __future__ import annotations

import random
import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_layout import iter_sessions  # noqa: E402
from isabelle_query import shape  # noqa: E402
from isabelle_query.parsing import sections_for_session  # noqa: E402


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = {a.split("=")[0]: a.split("=")[1] for a in sys.argv[1:]
           if a.startswith("--") and "=" in a}
    limit = int(opt.get("--limit", 0)) or None
    per = int(opt.get("--per", 6))
    rng = random.Random(int(opt.get("--seed", 1)))

    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    forms: Counter[str] = Counter()
    pools: dict[str, list[str]] = {}
    seen: set = set()
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            src = sec.source()
            for e in sec.entries:
                for st in shape._scan_steps(sec, e):
                    if not st.stmt_text or st.stmt_start == st.line:
                        continue
                    nxt = src[st.stmt_start - 1]
                    indent = len(nxt) - len(nxt.lstrip())
                    head = shape._WRAPPED_HEAD_RE.match(nxt, indent)
                    form = ("where+label" if head.group("where")
                            and head.end() > indent + len(head.group("where"))
                            else "where" if head.group("where")
                            else "label" if head.end() > indent else "bare")
                    form = f"{st.goal_cmd or st.kw}:{form}"
                    forms[form] += 1
                    pools.setdefault(form, []).append(
                        f"{sec.theory}:{st.line}  "
                        f"{src[st.line - 1].strip()[:40]}  /  "
                        f"{nxt.strip()[:60]}")
    print("wrapped statements read, by command and what precedes the "
          "delimiter:\n")
    for form, n in forms.most_common():
        print(f"  {n:7,}  {form}")
        pool = pools[form]
        for ex in rng.sample(pool, min(per, len(pool))):
            print(f"           {ex}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
