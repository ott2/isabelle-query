#!/usr/bin/env python3
r"""Entries whose span ends before their proof does [early-end].

An entry's `thy_end` is the line before the next boundary: the next entry, a
heading (`outline`), or a span-bounding command (`_structural_command_lines`).
A heading is legal inside a proof, and a boundary word can lead a line inside
one without being a command (`context.safe_unfolds` in a `note` list), so a
proof can run past its entry's end.  For every proof this asks whether it has
closed by `thy_end` (`parsing._proof_close_line`); if not, whether it closes
before the NEXT ENTRY, and what cut it.

Cost is reported in walk counts and walked lines, not seconds: the proofs a
fix would have to walk (those whose span is cut by a heading or a command
rather than by the next entry), against all proof lines.

    python scripts/probe_early_end.py [ROOT] [--limit=N] [--show=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query.parsing import (
    _LEADING_CMD_RE, _heading_at, _proof_close_line, _proof_follows,
    sections_for_session)


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 4))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    proofs = proof_lines = 0
    cut_by_other = walked = 0          # what a lazy fix would walk
    truncated: Counter[str] = Counter()
    lost_lines: Counter[str] = Counter()
    unclosed = 0
    by_heading = heading_walk = 0
    gated = gated_walk = 0
    never: list[str] = []
    examples: dict[str, list[str]] = defaultdict(list)
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            lines, outer = sec.source(), sec.outer_source()
            placed = sorted((e for e in sec.entries if e.thy_line),
                            key=lambda e: e.thy_line)
            starts = [e.src_start for e in placed]
            for k, e in enumerate(placed):
                if not e.proof_line:
                    continue
                proofs += 1
                proof_lines += max(0, e.thy_end - e.proof_line + 1)
                nxt = starts[k + 1] - 1 if k + 1 < len(starts) else len(lines)
                if e.thy_end >= nxt:
                    continue                 # cut by the next entry itself
                cut_by_other += 1
                walked += e.thy_end - e.proof_line + 1
                b0 = e.thy_end + 1
                while b0 <= len(lines) and not lines[b0 - 1].strip():
                    b0 += 1
                if b0 <= len(lines) and _heading_at(lines, b0 - 1) is not None:
                    by_heading += 1
                    heading_walk += e.thy_end - e.proof_line + 1
                    # The cheap gate: does a PROOF command follow the heading?
                    if _proof_follows(outer, b0, nxt):
                        gated += 1
                        gated_walk += e.thy_end - e.proof_line + 1
                if _proof_close_line(outer, e.proof_line, e.thy_end):
                    continue
                close = _proof_close_line(outer, e.proof_line, nxt)
                if not close:
                    unclosed += 1
                    if len(never) < 8:
                        never.append(f"{sec.path.relative_to(root)}:"
                                     f"{e.proof_line} {e.name}")
                    continue
                # What cut it: the first non-blank line after thy_end.
                b = e.thy_end + 1
                while b <= len(lines) and not lines[b - 1].strip():
                    b += 1
                if _heading_at(lines, b - 1) is not None:
                    why = "heading"
                else:
                    m = _LEADING_CMD_RE.match(outer[b - 1].lstrip())
                    word = m.group(1) if m else "?"
                    after = outer[b - 1].lstrip()[len(word):][:1]
                    why = f"command `{word}`" + (
                        " (qualified name)" if after == "." else "")
                truncated[why] += 1
                lost_lines[why] += close - e.thy_end
                if len(examples[why]) < show:
                    examples[why].append(
                        f"{sec.path.relative_to(root)}:{b} {e.name} "
                        f"(ends {e.thy_end}, proof closes {close})")
    print(f"{proofs:,} proofs, {proof_lines:,} proof lines")
    print(f"cut by a heading/command, not the next entry: {cut_by_other:,} "
          f"proofs, {walked:,} lines to walk "
          f"({100 * walked / max(1, proof_lines):.1f}% of proof lines)")
    print(f"  of them cut by a heading: {by_heading:,} proofs, "
          f"{heading_walk:,} lines "
          f"({100 * heading_walk / max(1, proof_lines):.1f}%)")
    print(f"  of them followed by a proof command: {gated:,} proofs, "
          f"{gated_walk:,} lines")
    print(f"never close before the next entry: {unclosed:,}")
    for n in never:
        print(f"            {n}")
    print(f"truncated: {sum(truncated.values()):,} proofs, "
          f"{sum(lost_lines.values()):,} lines outside their entry")
    for why, n in truncated.most_common():
        print(f"  {n:6,}  {lost_lines[why]:8,} lines  {why}")
        for ex in examples[why]:
            print(f"            {ex}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
