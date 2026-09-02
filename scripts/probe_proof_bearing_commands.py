#!/usr/bin/env python3
r"""Probe: which COMMANDS own proofs that `query` never scans?

`probe_step_alignment.py` splits the step-model divergence four ways, and the
largest bucket is OUTSIDE: 16,290 proof commands on lines that lie in no proof
body `query` scanned at all.  Those are not classifier failures — the scanner
was never pointed at them.

    interpretation dual: abstract_boolean_algebra ...   HOL/Boolean_Algebras:140
      apply standard                                    <- five proof commands,
           apply (rule disj_conj_distrib)                  none of them scanned
          apply (rule conj_disj_distrib)
         apply simp_all
      done

`interpretation` states a goal and proves it, but it declares no fact, so it is
not an `Entry` and has no `proof_line`.  This attributes every proof command to
the theory-level command that owns it and reports which owners `query` follows
into and which it does not — so the question "should the entry model index
proof-bearing commands that declare nothing?" is answered with a list and a
count rather than an impression.

Usage:
    probe_proof_bearing_commands.py SESSION [THEORY]
    probe_proof_bearing_commands.py ALL
"""
from __future__ import annotations

import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from probe_export_oracle import (  # noqa: E402
    _ENTITY_RE, _attrs, _available_sessions, _find_db, _read_export,
    _resolve_source, _theories)
from probe_step_alignment import (  # noqa: E402
    PROOF_KINDS, STRUCTURAL_KEYWORDS, isabelle_commands, query_steps)

# A command that opens a theory-level item.  `thy_goal*` states something to be
# proved; `thy_decl*` may still carry a proof (`instance ... ..`).
THY_KINDS_PREFIX = "thy_"


def source_path(db: Path, theory: str) -> Path | None:
    for kind in ("theory/thms", "theory/consts", "theory/types"):
        body = _read_export(db, theory, kind)
        if not body:
            continue
        for m in _ENTITY_RE.finditer(body):
            src = _attrs(m.group(1)).get("file", "")
            if src:
                return _resolve_source(src, {})
    return None


def survey(db: Path, theory: str, owners: Counter, scanned: Counter,
           samples: dict[str, list[str]]) -> bool:
    cmds, source = isabelle_commands(db, theory)
    if cmds is None:
        return False
    path = source_path(db, theory)
    if path is None:
        return False
    on_disk = path.read_text(encoding="utf-8", errors="replace")
    if source.rstrip("\n") != on_disk.rstrip("\n"):
        return False          # stale database; see probe_step_alignment.py
    try:
        _by_line, in_proof, thy = query_steps(path)
    except Exception:  # noqa: BLE001
        return False

    src = on_disk.splitlines()
    owner = None
    owner_line = 0
    for kw, kind, start, _end in cmds:
        if kind.startswith(THY_KINDS_PREFIX):
            owner, owner_line = kw, start
            continue
        if kind not in PROOF_KINDS or kw in STRUCTURAL_KEYWORDS:
            continue
        if owner is None:
            continue
        owners[owner] += 1
        if start in in_proof:
            scanned[owner] += 1
        elif len(samples.setdefault(owner, [])) < 3:
            head = src[owner_line - 1].strip()[:64] if owner_line <= len(src) \
                else ""
            samples[owner].append(f"{thy}:{owner_line}  {head}")
    return True


def main() -> None:
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    if not args:
        sys.exit(__doc__)
    if args[0] == "ALL":
        targets = _available_sessions()
    else:
        db = _find_db(args[0])
        if db is None:
            sys.exit(f"no database for {args[0]!r}")
        targets = [(args[0], db)]
    want = args[1] if len(args) > 1 else None

    owners: Counter[str] = Counter()
    scanned: Counter[str] = Counter()
    samples: dict[str, list[str]] = {}
    seen: set[str] = set()
    done = 0
    for name, db in targets:
        for t in _theories(db, name):
            stem = t.split(".")[-1]
            if stem in seen or (want and stem != want and t != want):
                continue
            if survey(db, t, owners, scanned, samples):
                seen.add(stem)
                done += 1

    total = sum(owners.values())
    miss = total - sum(scanned.values())
    print(f"=== {done} theories ===")
    print(f"proof commands attributed to an owning command   {total:>8,}")
    print(f"  on a line query scans                          "
          f"{total - miss:>8,}")
    print(f"  on a line query does NOT scan                  {miss:>8,}"
          f"   ({100.0 * miss / max(total, 1):.1f}%)")
    print("\nby owning command, worst coverage first:")
    print(f"  {'command':<22} {'proof cmds':>11} {'unscanned':>10}  rate")
    rows = sorted(owners.items(),
                  key=lambda kv: -(kv[1] - scanned[kv[0]]))
    for kw, n in rows:
        gap = n - scanned[kw]
        if not gap:
            continue
        print(f"  {kw:<22} {n:>11,} {gap:>10,}  {100.0 * gap / n:>5.1f}%")
    print("\n  clean owners (every proof command scanned):")
    clean = [kw for kw, n in owners.items() if n == scanned[kw]]
    print("    " + (", ".join(sorted(clean)) if clean else "(none)"))
    print("\nexamples of an unscanned owner:")
    for kw, _n in rows[:8]:
        for s in samples.get(kw, [])[:2]:
            print(f"  {kw:<18} {s}")


if __name__ == "__main__":
    main()
