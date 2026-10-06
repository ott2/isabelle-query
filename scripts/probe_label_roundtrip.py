#!/usr/bin/env python3
"""Does every theory's label resolve back to that theory? [label-depth]

A label is output and input: `theory_labels` prints it and `_resolve_theory`
reads it back.  This parses ROOT once and, for every theory, resolves its own
label, printing each one that lands elsewhere or nowhere.  Must print 0.

Before [label-depth], the AFP gave 1: the genuine
`Separation_Logic_Imperative_HOL/Automation` printed the same label as
Van_Emde_Boas_Trees' copy and resolved to the copy.

`Path.resolve` is memoised for the run: the resolver resolves every
section's path on every call, which is a syscall per section per label --
10^8 over the AFP -- and the answer does not change within one run.

Usage: probe_label_roundtrip.py ROOT
"""
import functools
import pathlib
import sys
from pathlib import Path

from isabelle_query import commands
from isabelle_query.api import parse_root
from isabelle_query.model import theory_labels


def main() -> int:
    pathlib.Path.resolve = functools.lru_cache(maxsize=None)(
        pathlib.Path.resolve)
    sections = parse_root(Path(sys.argv[1]))
    labels = theory_labels(sections)
    bad = 0
    seen = set()
    for sec in sections:
        p = sec.path.resolve()
        if p in seen:
            continue
        seen.add(p)
        got = commands._resolve_theory(sections, labels[p])
        if got is None or got.path.resolve() != p:
            bad += 1
            print(f"  {labels[p]}: {p} -> {got.path if got else None}")
    print(f"{len(seen)} theories, {bad} labels that do not round-trip")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
