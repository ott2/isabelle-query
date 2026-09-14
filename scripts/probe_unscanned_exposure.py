#!/usr/bin/env python3
r"""How much proof text sits outside the census, corpus-wide [proof-bearing-commands].

`probe_proof_bearing_commands.py` answers this precisely, by diffing `query`'s
steps against Isabelle's own `command_span` markup — but it needs a built
session database, so it reaches 687 theories and cannot see the AFP at all.
`todo.md`'s "~2% of the corpus" comes from that sample.  Whether to hold a
release for this rests on that rate, and an unbuilt corpus is 11,604 theories,
so the rate wants re-measuring where the code actually runs.

This trades precision for reach: no markup, no step classification, just the
command-position scan `probe_missing_decl_commands.py` uses, measuring the
LINES each proof-bearing command owns (from the command to the next
command-position line) against the proof lines `query` does scan.  Owned lines
over-count steps — a line may be blank or a continuation — but it over-counts
both populations equally, so the RATIO is the number to read.

    python scripts/probe_unscanned_exposure.py [--limit N] [--commands a,b,c]

`--commands` re-points the scan at any command list — `[decl-commands]`'s
undeclared goal commands (`proposition,schematic_goal,lemmas`) size the same
way, and sizing both against one denominator is the point: two queued changes
that each move the census want comparing before either ships.

`--limit` takes the first N AFP entries ALPHABETICALLY, which is a prefix and
not a sample; it is for smoke-testing this script, not for quoting.
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

# Commands that state and prove a goal but declare no citable fact, so they are
# not an `Entry` and `shape` never follows them.  From `todo.md`'s table.
PROOF_BEARING = ("instance", "sublocale", "interpretation",
                 "global_interpretation", "subclass", "termination",
                 "notepad", "lift_definition")

_CMD_RE = re.compile(r"^([a-z_]+)\b")


def main() -> None:
    limit = None
    if "--limit" in sys.argv:
        limit = int(sys.argv[sys.argv.index("--limit") + 1])
    commands = PROOF_BEARING
    if "--commands" in sys.argv:
        commands = tuple(w.strip() for w in
                         sys.argv[sys.argv.index("--commands") + 1].split(","))

    paths: list[Path] = []
    if AFP.is_dir():
        ents = sorted(d for d in AFP.iterdir() if d.is_dir())
        for ent in (ents[:limit] if limit else ents):
            paths.extend(sorted(ent.rglob("*.thy")))
    for sub in ("HOL", "FOL", "ZF"):
        if (DIST / sub).is_dir():
            paths.extend(sorted((DIST / sub).rglob("*.thy")))

    occurrences: Counter[str] = Counter()
    owned_lines: Counter[str] = Counter()
    scanned_proof_lines = 0
    n_thy = 0

    for p in paths:
        try:
            sec = cli._parse_one(p.stem, p)
        except Exception:  # noqa: BLE001 — a corpus has unparseable files
            continue
        n_thy += 1
        outer = sec.outer_source()
        # Command position is column 0 in the OUTER view, the same test the
        # decl probe uses: terms are blanked there, so an indented continuation
        # of a term cannot masquerade as a command.
        cmd_at = [i for i, line in enumerate(outer, start=1)
                  if line.strip() and not line[:1].isspace()]
        for i in cmd_at:
            m = _CMD_RE.match(outer[i - 1].lstrip())
            if m is None or m.group(1) not in commands:
                continue
            nxt = next((c for c in cmd_at if c > i), len(outer) + 1)
            occurrences[m.group(1)] += 1
            owned_lines[m.group(1)] += nxt - i
        # The denominator: proof lines that ARE scanned, i.e. inside an entry's
        # proof body.  `proof_line` is unset for a bare definition.
        for e in sec.entries:
            if e.proof_line and e.body_end_line:
                scanned_proof_lines += max(0, e.body_end_line - e.proof_line + 1)

    total_occ = sum(occurrences.values())
    total_owned = sum(owned_lines.values())
    print(f"=== {n_thy:,} theories ===\n")
    print(f"{'command':<24}{'occurrences':>13}{'owned lines':>14}"
          f"{'lines/occ':>11}")
    for kw, n in occurrences.most_common():
        ln = owned_lines[kw]
        print(f"  {kw:<22}{n:>13,}{ln:>14,}{ln / n:>11.1f}")
    print(f"  {'TOTAL':<22}{total_occ:>13,}{total_owned:>14,}"
          f"{(total_owned / total_occ if total_occ else 0):>11.1f}")

    denom = scanned_proof_lines + total_owned
    print(f"\nproof lines query DOES scan: {scanned_proof_lines:,}")
    print(f"proof lines it does not:     {total_owned:,}")
    print(f"unscanned share of all proof text: "
          f"{total_owned / denom:.2%}" if denom else "")


if __name__ == "__main__":
    raise SystemExit(main())
