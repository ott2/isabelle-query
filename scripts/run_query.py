#!/usr/bin/env python3
r"""Run `query` from whichever `isabelle_query` is first on `sys.path`.

For old-against-new comparisons: extract the old tree with
`git archive HEAD src | tar -x -C .stage/old`, then

    PYTHONPATH=$PWD/.stage/old/src python scripts/run_query.py ARGS...
    python scripts/run_query.py ARGS...

The package's file goes to stderr first, because a `PYTHONPATH` entry that
does not exist falls back silently to the installed package, and then both
runs measure the same code.
"""

import sys

import isabelle_query
from isabelle_query import cli

print(f"# {isabelle_query.__file__}", file=sys.stderr)
sys.argv[0] = "query"
cli.main()
