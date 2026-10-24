#!/usr/bin/env python3
r"""Does `api.resolve_theories` read loci as the CLI does? (#34)

Loads ROOT the way the CLI does (a full parse), then checks over every
theory:

1. the headers-only walk `resolve_theories` reads lists the same theories,
   in the same order, as the CLI's loaded sections;
2. every label `theory_labels` prints resolves to exactly its own file;
3. for every bare name and a seeded sample of the labels with a separator,
   the first candidate is the file the CLI's `_resolve_theory` picks, and a
   bare name shared by several theories lists them all.  (The CLI scans per
   call, a path resolve per theory; every label would take an hour.)

    python scripts/probe_theory_resolver.py [ROOT] [--sample=N]
"""

from __future__ import annotations

import random
import sys
from collections import Counter
from pathlib import Path

from isabelle_query import api
from isabelle_query.commands import _resolve_theory
from isabelle_query.model import theory_labels
from isabelle_query.parsing import _root_theories


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = dict(a.split("=", 1) for a in sys.argv[1:] if "=" in a)
    n_sample = int(opt.get("--sample", 300))
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    sections = api.parse_root(root)
    walk, seen = [], set()
    for name, path in _root_theories(root)[0]:
        if path.exists() and path.resolve() not in seen:
            seen.add(path.resolve())
            walk.append((name, path.resolve()))
    loaded = [(s.theory, s.path.resolve()) for s in sections]
    print(f"1. walk == loaded: {walk == loaded} "
          f"({len(walk):,} vs {len(loaded):,} theories)")

    labels = theory_labels(sections)
    bare = sorted({s.theory for s in sections})
    got = api.resolve_theories(list(labels.values()) + bare, root=root)
    bad_label = [(lab, got[lab]) for p, lab in labels.items()
                 if got[lab] != [p]]
    print(f"2. labels resolving to exactly their own file: "
          f"{len(labels) - len(bad_label):,} of {len(labels):,}")
    for lab, hits in bad_label[:10]:
        print(f"   {lab} -> {[str(h) for h in hits]}")

    random.seed(0)
    pathy = [lab for lab in labels.values() if "/" in lab]
    checked = bare + random.sample(pathy, min(n_sample, len(pathy)))
    disagree = []
    for name in checked:
        cli = _resolve_theory(sections, name)
        first = got[name][0] if got[name] else None
        if (cli.path.resolve() if cli else None) != first:
            disagree.append(name)
    shared = Counter(s.theory for s in sections)
    multi = [n for n in bare if shared[n] > 1]
    listed = sum(len(got[n]) == shared[n] for n in multi)
    print(f"3. first candidate == CLI's answer: "
          f"{len(checked) - len(disagree):,} of {len(checked):,} "
          f"({len(pathy):,} labels have a separator); shared bare names "
          f"listing every "
          f"theory: {listed:,} of {len(multi):,}")
    for name in disagree[:10]:
        print(f"   {name}")
    return 0 if walk == loaded and not bad_label and not disagree else 1


if __name__ == "__main__":
    sys.exit(main())
