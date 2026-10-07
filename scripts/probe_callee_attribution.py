#!/usr/bin/env python3
r"""Probe: which declaration does a callee row name?  [callee-attribution]

Issue #18: the call graph is keyed by NAME, and `--reach closure` asks
visibility per name -- "can this theory see SOME `sim_tape`?" -- but the row a
verb prints names one declaration, chosen first-wins by `_entry_by_name`.  When
a name has several declarations the two disagree, and the row can name one the
citing theory cannot see.

For every edge `caller -> callee` of the closure-scoped graph whose caller has
a single declaration, and whose callee is declared in more than one theory
(repeats inside one theory are a different question), this classifies the
first-wins row against the declarations the caller's theory can actually see:

    right       the first-wins declaration is visible, and is the only one
    invisible   the first-wins declaration is NOT visible (the issue's bug)
    several     declarations in several visible theories (first-wins hides some)
    unknown     the caller's closure could not be read (no filter applies)

Usage:  probe_callee_attribution.py [ROOT] [--samples N]   (default: the AFP)
"""
from __future__ import annotations

import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_query import cli, graph  # noqa: E402


def main() -> None:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    k = int(sys.argv[sys.argv.index("--samples") + 1]) \
        if "--samples" in sys.argv else 8
    if "--samples" in sys.argv:
        args = [a for a in args if a != str(k)]
    root = Path(args[0]).expanduser() if args else (
        Path.home() / "repos" / "afp" / "thys")
    cli._ROOT_OVERRIDE = root.resolve()
    sections = cli.load_index()
    g = graph._build_call_graph(sections, reach="closure")

    decls: dict[str, list[str]] = defaultdict(list)    # name -> theories
    for sec in sections:
        for e in sec.entries:
            decls[e.name].append(sec.theory)
    first = graph._entry_by_name(sections)
    vis = graph._Visibility(sections, "closure")

    # Group by the caller's theory so the single-slot closure cache holds.
    by_thy: dict[str, list[tuple[str, str]]] = defaultdict(list)
    edges = multi = 0
    for caller, cs in g.callees.items():
        if ":<toplevel>" in caller or len(decls.get(caller, ())) != 1:
            continue
        for callee in cs:
            edges += 1
            if len(set(decls.get(callee, ()))) > 1:
                multi += 1
                by_thy[decls[caller][0]].append((caller, callee))

    tally: Counter[str] = Counter()
    samples: dict[str, list[str]] = defaultdict(list)
    for thy, pairs in by_thy.items():
        reach = vis.closure(thy)
        for caller, callee in pairs:
            if reach is None:
                kind = "unknown"
            else:
                seen = {t for t in decls[callee] if t in reach}
                if first[callee][0] not in reach:
                    kind = "invisible"
                elif len(seen) > 1:
                    kind = "several"
                else:
                    kind = "right"
            tally[kind] += 1
            samples[kind].append(f"{thy}: {caller} -> {callee} "
                                 f"(first-wins {first[callee][0]}; "
                                 f"declared in {sorted(set(decls[callee]))})")

    print(f"=== {len(sections):,} theories under {root} ===")
    print(f"edges from single-declaration callers: {edges:,}")
    print(f"  callee declared in several theories: {multi:,}")
    for kind in ("right", "invisible", "several", "unknown"):
        print(f"    {kind:<10} {tally[kind]:>9,}")
    rnd = random.Random(0)
    for kind in ("invisible", "several"):
        xs = samples[kind]
        if xs:
            print(f"\n{kind} (random sample):")
            for x in rnd.sample(xs, min(k, len(xs))):
                print(f"  {x}")


if __name__ == "__main__":
    main()
