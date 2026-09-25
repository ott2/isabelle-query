#!/usr/bin/env python3
"""How much does [bound-name-reach] actually change `callers`?

The PR that introduced it argues a name an entry BINDS is declared where its
binder is, so a single-name scan may scope it like an entry.  That is a
narrowing: a theory the closure excludes stops being reported.  This measures
the narrowing on a real corpus, per bound name, and — because the filter's
licence is "drop only what the citing theory positively cannot see" — prints
the dropped loci so each can be checked by hand.

Both filters are built in ONE process from the same parse, so the delta is the
rule and nothing else:

    old   _Visibility(sections, "closure")          entry names only
    new   _Visibility(sections, "closure", bound_names=True)

Needs `_Visibility(..., bound_names=True)`, which arrived with
[bound-name-reach] — `git log --grep='\[bound-name-reach\]'`.  Written to
review that change; kept to re-measure the narrowing whenever the rule moves.

Usage:  python3 scripts/probe_bound_name_reach.py <corpus-dir> [max-names]
"""
from __future__ import annotations

import sys
from pathlib import Path

from isabelle_query.graph import _Visibility
from isabelle_query.parsing import _sections_from_dir


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    root = Path(sys.argv[1]).expanduser()
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 0

    sections: list = []
    _sections_from_dir(root, set(), sections)
    print(f"{root}: {len(sections)} sections, "
          f"{sum(len(s.entries) for s in sections)} entries")

    old = _Visibility(sections, "closure")
    new = _Visibility(sections, "closure", bound_names=True)

    # Every name an entry binds that is NOT itself an entry name: those are
    # exactly the names whose scoping the change invents.
    entry_names = {e.name for s in sections for e in s.entries if e.name}
    bound: dict[str, str] = {}
    for s in sections:
        for e in s.entries:
            for n in e.bound_names:
                if n and n not in entry_names:
                    bound.setdefault(n, f"{s.theory} ({e.name})")
    names = sorted(bound)
    if cap:
        names = names[:cap]
    print(f"{len(bound)} bound-only names; checking {len(names)}\n")

    changed = 0
    total_drops = 0
    for n in names:
        drops = [s.theory for s in sections
                 if old.sees(s.theory, n) and not new.sees(s.theory, n)]
        adds = [s.theory for s in sections
                if new.sees(s.theory, n) and not old.sees(s.theory, n)]
        if drops or adds:
            changed += 1
            total_drops += len(drops)
            print(f"{n}  (bound in {bound[n]})")
            if drops:
                print(f"    -{len(drops)}: {', '.join(sorted(drops)[:8])}")
            if adds:
                print(f"    +{len(adds)}: {', '.join(sorted(adds)[:8])}")
    print(f"\n{changed}/{len(names)} names re-scoped, "
          f"{total_drops} theory-level drops")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
