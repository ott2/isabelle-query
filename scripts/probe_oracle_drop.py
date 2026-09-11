#!/usr/bin/env python3
r"""Why the corpus differential test drops edges [oracle-drop-rate].

`tests/test_corpus.py::test_fast_call_graph_matches_oracle_on_subset` compares
`cli._build_call_graph` against `tests/support.brute_force_call_graph` over the
alphabetically-first N `.thy` files and allows the fast side to drop
`_MAX_DROP_FRACTION` of the caller-edges.  It is RED.

The ceiling's stated justification is a per-name over-match in the reference
(a short symbolic name inside a longer identifier), which is a handful of
edges.  But the two sides do not run the same rule: `_build_call_graph`
defaults to `reach="closure"` and the reference has no reach filter at all, so
every edge the VISIBILITY rule drops [citation-reach] also counts against that
ceiling.  This probe separates the two populations instead of guessing:

    python scripts/probe_oracle_drop.py [--corpus DIR] [--subset N]

Prints the drop count under each reach mode.  `closure` is what the test
measures; `name` is the same fast builder with the visibility filter off, i.e.
the like-for-like comparison the ceiling was written for.  The gap between them
is the reach rule, not a builder divergence.  Also times each phase, because
the same test got ~5x slower with no code change to the builder.
"""

from __future__ import annotations

import argparse
import glob
import os
import sys
import time
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))
sys.path.insert(0, str(_ROOT / "tests"))

from isabelle_query import cli, graph  # noqa: E402
from support import brute_force_call_graph  # noqa: E402


def edges(g) -> set[tuple[str, str]]:
    return {(caller, name) for name, cs in g.callers.items() for caller in cs}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default=os.environ.get(
        "ISABELLE_QUERY_CORPUS", str(Path.home() / "repos" / "afp" / "thys")))
    ap.add_argument("--subset", type=int, default=120)
    args = ap.parse_args()

    t0 = time.monotonic()
    files = sorted(glob.glob(os.path.join(args.corpus, "**", "*.thy"),
                             recursive=True))
    t_glob = time.monotonic() - t0
    print(f"{len(files):,} .thy files under {args.corpus}  ({t_glob:.1f}s)")

    # Mirror the test's setUpClass exactly: the custom-command union is built
    # from the WHOLE corpus, not the subset, so a theory using a command that
    # another entry declares still parses.  Timed separately because it reads
    # every header in the corpus while the graph work only touches the subset.
    t0 = time.monotonic()
    cli._CUSTOM_COMMANDS.clear()
    cli._populate_custom_commands([(Path(p).stem, Path(p)) for p in files])
    t_custom = time.monotonic() - t0
    print(f"custom-command union over all files: {t_custom:.1f}s "
          f"({len(cli._CUSTOM_COMMANDS):,} commands)")

    subset = files[:args.subset]
    entries = sorted({Path(p).relative_to(args.corpus).parts[0]
                      for p in subset})
    print(f"\nsubset = first {len(subset)} files, spanning {len(entries)} "
          f"entries: {', '.join(entries)}")

    t0 = time.monotonic()
    secs = [cli._parse_one(Path(p).stem, Path(p)) for p in subset]
    t_parse = time.monotonic() - t0
    n_entries = sum(len(s.entries) for s in secs)
    print(f"parsed {len(secs)} theories / {n_entries:,} entries  "
          f"({t_parse:.1f}s)")

    t0 = time.monotonic()
    ref = brute_force_call_graph(secs)
    t_ref = time.monotonic() - t0
    ref_edges = edges(ref)
    print(f"reference (name-only, no reach filter): {len(ref_edges):,} edges  "
          f"({t_ref:.1f}s)")

    by_mode = {}
    for mode in graph.REACH_MODES:
        t0 = time.monotonic()
        g = cli._build_call_graph(secs, reach=mode)
        dt = time.monotonic() - t0
        by_mode[mode] = g
        got = edges(g)
        dropped = ref_edges - got
        invented = got - ref_edges
        frac = len(dropped) / max(1, len(ref_edges))
        print(f"  reach={mode:8} {len(got):7,} edges   "
              f"dropped {len(dropped):5,} ({frac:.2%})   "
              f"invented {len(invented):3}   ({dt:.1f}s)")

    # The whole question: how much of the closure-mode drop is the reach rule?
    d_closure = ref_edges - edges(by_mode["closure"])
    d_name = ref_edges - edges(by_mode["name"])
    reach_only = d_closure - d_name
    print(f"\ndrop attributable to the REACH rule alone: {len(reach_only):,} "
          f"of {len(d_closure):,}")
    print(f"drop present with reach OFF (a real builder divergence): "
          f"{len(d_name):,}")

    per_name: Counter[str] = Counter(name for _c, name in reach_only)
    print("\nnames losing the most to the reach rule:")
    for name, n in per_name.most_common(15):
        print(f"  {name:40} -{n}")

    if d_name:
        print("\nthe reach-independent residual, in full "
              "(this is what the ceiling was written for):")
        for caller, name in sorted(d_name)[:40]:
            print(f"  {caller}  ->  {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
