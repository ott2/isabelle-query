#!/usr/bin/env python3
"""Does each synthetic `THEORY:<toplevel>` caller name exactly one theory?

A citation outside every entry is attributed to a per-theory node.  It was
named by the BARE theory name, so same-named theories (AFP has nineteen
`Examples`) shared one node [toplevel-label]; it is now named by the locus
label.  This prints the node count -- 4,874 under the bare name, 5,244 under
the label on the 2025-2 AFP, so 370 theories had been folded into another's
node -- and any node whose prefix names more than one theory.  That is 0
but for one label `theory_labels` itself gets wrong [label-depth].

Usage: probe_toplevel_collisions.py ROOT
"""
import sys
from collections import Counter
from pathlib import Path

from isabelle_query import cli
from isabelle_query.api import parse_root
from isabelle_query.model import locus_labels

SUFFIX = ":<toplevel>"


def main() -> int:
    sections = parse_root(Path(sys.argv[1]))
    graph = cli._build_call_graph(sections)
    per_label = Counter(locus_labels(sections).values())
    nodes = {c for cs in graph.callers.values() for c in cs
             if c.endswith(SUFFIX)}
    shared = sorted(n for n in nodes if per_label[n[:-len(SUFFIX)]] != 1)
    print(f"{len(sections)} theories, {len(nodes)} <toplevel> nodes, "
          f"{len(shared)} not naming exactly one theory")
    for n in shared:
        print(f"  {n}: {per_label[n[:-len(SUFFIX)]]} theories")
    return 1 if shared else 0


if __name__ == "__main__":
    sys.exit(main())
