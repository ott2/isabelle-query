#!/usr/bin/env python3
"""How often does `Entry.body_end_line` stop INSIDE a proof? [body-end-text]

`body_end_line` is documented to stop before a trailing inter-lemma `text` /
`\\<comment>` block.  A `text` block is also legal in proof mode, and one written
mid-proof ends the body there: `Ford_Fulkerson.flow_value` ends at line 36
while its `qed` is at 89.  Every consumer that walks `proof_line ..
body_end_line` — the `shape` step scan, `enclosing`'s block drill-down — then
sees half a proof.  Found while building `unused --locals`, which walks to
where the proof ends instead.

Compares `body_end_line` with where the proof actually ends, as
`proof_locals.proof_end` walks it — the entry's outermost `qed` or the
terminator of its goal.  Not "is there a proof command before `thy_end`":
that also counts the proof of an `instance` or `termination` that follows
the entry, which is `[proof-bearing-commands]`, a different gap.

Usage:  python3 scripts/probe_body_end_text.py <corpus-dir>
"""
from __future__ import annotations

import sys
from pathlib import Path

from isabelle_query.parsing import _sections_from_dir
from isabelle_query.proof_locals import proof_end


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    corpus = Path(sys.argv[1]).expanduser()
    proofs = cut = lost = 0
    examples: list[str] = []
    for root in sorted(p for p in corpus.iterdir() if (p / "ROOT").exists()):
        sections: list = []
        _sections_from_dir(root, set(), sections)
        for sec in sections:
            for e in sec.entries:
                if not e.proof_line or not e.body_end_line:
                    continue
                proofs += 1
                end = proof_end(sec, e)
                if end > e.body_end_line:
                    cut += 1
                    lost += end - e.body_end_line
                    if len(examples) < 10:
                        examples.append(f"{sec.path.relative_to(corpus)}:"
                                        f"{e.body_end_line} {e.name} "
                                        f"(proof continues to {end})")
    print(f"{proofs} proofs, {cut} cut short by a mid-proof text block "
          f"({cut / max(1, proofs):.3%}), {lost} proof lines unseen")
    print("\n".join(examples))
    return 0


if __name__ == "__main__":
    sys.exit(main())
