#!/usr/bin/env python3
r"""Probe: which fact-declaring commands does `DECL_RE` not know?

`probe_proof_bearing_commands.py` found `proposition` at 34.3% unscanned where
`theorem` is at 0.0% and `corollary` is clean — a split that no scope decision
explains, since all three are `thy_goal_stmt` in Isabelle and declare a fact
the same way.  `DECL_RE` simply lists `lemma|corollary|theorem` and not
`proposition`.

The consequence is worse than an omission.  An unrecognised command is not a
declaration boundary either, so the PRECEDING entry's span runs straight
through it and the unrecognised proof's steps are attributed to the lemma
above:

    lemma z: "True" by simp     <- body_end runs to the end of the theory
    proposition b: "True"          because nothing after it starts an entry
      by simp

so this counts both halves: declarations `query` cannot see, and the entries
whose spans over-run because of them.

Scanned in COMMAND POSITION (`outer_source`), so a word inside a term or a
comment cannot register — the same view `parsing` uses to find a declaration.

Usage:  probe_missing_decl_commands.py [--limit N]
"""
from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_query import cli  # noqa: E402

AFP = Path.home() / "repos" / "afp" / "thys"
DIST = Path("/Applications/Isabelle2025-2.app/src")

# Goal/definition commands that declare a citable fact and are NOT in DECL_RE.
# `private` / `qualified` are name-space MODIFIERS that may precede any of them
# (Pure/Isar, `private lemma foo:`), so they are matched as a prefix rather than
# as commands of their own.
CANDIDATES = ("proposition", "schematic_goal", "lemmas", "theorems",
              "named_theorems", "definition", "lemma", "theorem", "corollary")
MODIFIERS = ("private", "qualified")

_CMD_RE = re.compile(r"^([a-z_]+)\b")
_MOD_RE = re.compile(rf"^({'|'.join(MODIFIERS)})\s+([a-z_]+)\b")


def main() -> None:
    limit = None
    if "--limit" in sys.argv:
        limit = int(sys.argv[sys.argv.index("--limit") + 1])

    paths: list[Path] = []
    if AFP.is_dir():
        ents = sorted(d for d in AFP.iterdir() if d.is_dir())
        for ent in (ents[:limit] if limit else ents):
            paths.extend(sorted(ent.rglob("*.thy")))
    for sub in ("HOL", "FOL", "ZF"):
        if (DIST / sub).is_dir():
            paths.extend(sorted((DIST / sub).rglob("*.thy")))

    unseen: Counter[str] = Counter()
    seen: Counter[str] = Counter()
    modified: Counter[str] = Counter()
    samples: dict[str, list[str]] = {}
    overrun = 0
    n_thy = 0
    for p in paths:
        try:
            sec = cli._parse_one(p.stem, p)
        except Exception:  # noqa: BLE001
            continue
        n_thy += 1
        at = {e.thy_line: e for e in sec.entries}
        outer = sec.outer_source()
        for i, line in enumerate(outer, start=1):
            stripped = line.lstrip()
            if not stripped or line[:1].isspace():
                continue          # a declaration starts in column 0
            m_mod = _MOD_RE.match(stripped)
            word = None
            if m_mod:
                word = f"{m_mod.group(1)} {m_mod.group(2)}"
                modified[word] += (i not in at)
                if i not in at and len(samples.setdefault(word, [])) < 3:
                    samples[word].append(f"{sec.theory}:{i}  {stripped[:60]}")
                continue
            m = _CMD_RE.match(stripped)
            if m is None or m.group(1) not in CANDIDATES:
                continue
            word = m.group(1)
            if i in at:
                seen[word] += 1
                continue
            unseen[word] += 1
            if len(samples.setdefault(word, [])) < 3:
                samples[word].append(f"{sec.theory}:{i}  {stripped[:60]}")
        # An entry whose recorded body runs past a declaration `query` cannot
        # see is the over-run half.
        starts = sorted(at)
        for e in sec.entries:
            end = e.body_end_line or 0
            if not end:
                continue
            nxt = next((s for s in starts if s > e.thy_line), None)
            if nxt is None and end > e.thy_line + 200:
                overrun += 1

    print(f"=== {n_thy:,} theories ===")
    print("command-position occurrences with NO entry at that line:\n")
    print(f"  {'command':<22} {'no entry':>10} {'has entry':>10}  rate")
    for word in sorted(set(unseen) | set(seen), key=lambda w: -unseen[w]):
        n, s = unseen[word], seen[word]
        if not n:
            continue
        print(f"  {word:<22} {n:>10,} {s:>10,}  {100.0 * n / (n + s):>5.1f}%")
    print("\n  with a namespace modifier (never an entry today):")
    for word, n in modified.most_common():
        print(f"  {word:<22} {n:>10,}")
    print("\nexamples:")
    for word in sorted(samples, key=lambda w: -(unseen[w] + modified[w])):
        for s in samples[word][:2]:
            print(f"  {word:<18} {s}")
    print(f"\n  entries whose body runs >200 lines with no following "
          f"declaration: {overrun:,}")


if __name__ == "__main__":
    main()
