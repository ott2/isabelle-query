#!/usr/bin/env python3
"""Print `path<TAB>label` for every theory under ROOT, sorted by path.

Run before and after a change to `theory_labels` and diff the two files: every
changed line is a locus query prints differently [label-depth].

Usage: dump_theory_labels.py ROOT > labels.tsv
"""
import sys
from pathlib import Path

from isabelle_query.api import parse_root
from isabelle_query.model import theory_labels


def main() -> int:
    labels = theory_labels(parse_root(Path(sys.argv[1])))
    for p in sorted(labels):
        print(f"{p}\t{labels[p]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
