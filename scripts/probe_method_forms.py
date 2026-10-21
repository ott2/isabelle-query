#!/usr/bin/env python3
r"""The method forms of a corpus, and the check that `method_kinds` derives
from them [method-forms].

`methods` (#25) records `position:name/modifier` per proof.  `method_kinds`
is meant to be its `by:` / `apply:` forms bucketed by name, so a stored
census row stays comparable; this counts the proofs where that fails, and
prints the commonest forms with the modifiers that split them.

    python scripts/probe_method_forms.py [ROOT] [--limit=N] [--top=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

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
    top = int(opt.get("--top", 30))

    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    totals: Counter[str] = Counter()
    n_proofs = n_bad = 0
    bad: list[str] = []
    seen: set = set()
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            for e in sec.entries:
                pm = shape.analyze_proof(sec, e)
                if pm is None:
                    continue
                n_proofs += 1
                totals.update(pm.methods)
                derived = Counter({k: 0 for k in shape.METHOD_KIND_NAMES})
                for form, n in pm.methods.items():
                    pos, _, rest = form.partition(":")
                    if pos in ("by", "apply"):
                        derived[shape.method_kind(rest.split("/")[0])] += n
                if dict(derived) != shape.method_kind_counts(pm.steps):
                    n_bad += 1
                    if len(bad) < 10:
                        bad.append(f"{sec.theory}:{e.thy_line} {e.name}")
    print(f"{n_proofs:,} proofs; method_kinds NOT derivable from methods: "
          f"{n_bad:,}")
    for b in bad:
        print(f"  {b}")
    print(f"\n{len(totals):,} distinct forms, {sum(totals.values()):,} "
          f"applications; top {top}:")
    for form, n in totals.most_common(top):
        print(f"  {n:9,}  {form}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
