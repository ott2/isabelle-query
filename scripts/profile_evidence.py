#!/usr/bin/env python3
r"""Profile `unused`'s evidence pass (`commands._evidence`) over a corpus.

Loads once, then runs the pass under cProfile and prints the top entries by
cumulative time, so the cost of each part (antiquotation scan, visibility
index, per-mention checks) is read off one run, apart from load noise.

    python scripts/profile_evidence.py [ROOT] [N]
"""

import cProfile
import pstats
import sys
from pathlib import Path

from isabelle_query import cli, commands

root = Path(sys.argv[1]).expanduser() if len(sys.argv) > 1 else (
    Path.home() / "repos" / "afp" / "thys")
cli._ROOT_OVERRIDE = root.resolve()
sections = cli.load_index()
prof = cProfile.Profile()
prof.runcall(commands._evidence, sections)
pstats.Stats(prof).sort_stats("cumulative").print_stats(
    int(sys.argv[2]) if len(sys.argv) > 2 else 18)
