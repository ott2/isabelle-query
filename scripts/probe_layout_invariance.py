#!/usr/bin/env python3
r"""Does a census record move when only the layout does? [step-command]

#24: `n_steps` counted lines, so the same proof laid out two ways measured
differently.  The fix makes a step an Isar command, and the check that it
worked needs no taxonomy: move every proof command that does not start its
line onto a line of its own, re-parse, and compare each proof's census
record with the original's.  Only the fields that count lines may change.
Any other difference is a place where the scanner still reads the layout.

    python scripts/probe_layout_invariance.py [ROOT] [--limit=N] [--show=N]

Reuses the reflow and the record reduction of `tests/test_step_command.py`,
so the probe and the test cannot drift apart.  Both versions of a theory
are parsed by `cli._parse_one`, the reflowed one from `.stage/reflow/`.
`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))
sys.path.insert(0, str(_ROOT / "tests"))

from isabelle_layout import iter_sessions  # noqa: E402
from isabelle_query import cli  # noqa: E402
from test_step_command import records, reflow  # noqa: E402


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = {a.split("=")[0]: a.split("=")[1] for a in sys.argv[1:]
           if a.startswith("--") and "=" in a}
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 20))
    stage = _ROOT / ".stage" / "reflow"
    stage.mkdir(parents=True, exist_ok=True)

    from isabelle_query.parsing import sections_for_session
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    n_thy = n_moved = n_proofs = n_diff = 0
    fields: Counter[str] = Counter()
    examples: list[str] = []
    seen: set = set()
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            n_thy += 1
            text = reflow(sec)
            if text == "\n".join(sec.source()) + "\n":
                continue
            n_moved += 1
            tmp = stage / f"{sec.theory.replace('/', '__')}.thy"
            tmp.write_text(text, encoding="utf-8")
            try:
                flowed = cli._parse_one(sec.theory, tmp)
                before, after = records(sec), records(flowed)
            except Exception as exc:  # noqa: BLE001
                print(f"skip {sec.theory}: {exc}", file=sys.stderr)
                continue
            for name in before.keys() & after.keys():
                n_proofs += 1
                diff = [k for k in before[name] if k != "session"
                        and before[name][k] != after[name].get(k)]
                if diff:
                    n_diff += 1
                    fields.update(diff)
                    if len(examples) < show:
                        examples.append(
                            f"{sec.theory}:{name}  " + ", ".join(
                                f"{k} {before[name][k]!r}->"
                                f"{after[name].get(k)!r}" for k in diff[:3]))
    print(f"{n_thy:,} theories, {n_moved:,} with a command moved; "
          f"{n_proofs:,} proofs compared, {n_diff:,} records moved")
    for f, n in fields.most_common():
        print(f"  {n:7,}  {f}")
    for ex in examples:
        print(f"  {ex}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
