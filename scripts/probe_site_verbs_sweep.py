#!/usr/bin/env python3
"""Crash / contract sweep for the `instances` and `codeqs` scans.

The two site verbs parse command headers with grammars of their own, so the
question a corpus answers is not "is the count right" (no oracle) but "does
any real theory make the scan raise, hang, or break its own exit contract".
For each entry it picks the locales/classes and constants the entry itself
declares, runs both scans in-process, and reports exceptions.

`instances -r` is included, because the hierarchy walk is the one path with a
cycle risk and the one that was 15x slower before the perf commit.

Needs `isabelle_query.sites`, which arrived with [instantiation-sites] /
[code-equations].  Re-run it after any change to either scan: the grammars are
hand-written, so "no real theory makes this raise" is the only cheap invariant
they have.

Usage:  python3 scripts/probe_site_verbs_sweep.py <corpus-dir> [max-entries]
"""
from __future__ import annotations

import sys
import time
import traceback
from pathlib import Path

from isabelle_query.parsing import _sections_from_dir
from isabelle_query.sites import (
    CONSTANT_TAGS,
    LOCALE_TAGS,
    find_code_equations,
    find_instantiations,
    find_instantiations_transitive,
)

PER_ENTRY = 12          # subjects per kind per entry — a sample, not a census


def sweep(root: Path) -> tuple[int, int, float]:
    sections: list = []
    _sections_from_dir(root, set(), sections)
    if not sections:
        return 0, 0, 0.0

    locales, consts = [], []
    for s in sections:
        for e in s.entries:
            if not e.name:
                continue
            if e.tag in LOCALE_TAGS:
                locales.append(e.name)
            elif e.tag in CONSTANT_TAGS:
                consts.append(e.name)

    checked = fails = 0
    t0 = time.time()
    for name in sorted(set(locales))[:PER_ENTRY]:
        for fn in (find_instantiations, find_instantiations_transitive):
            checked += 1
            try:
                fn(sections, name)
            except Exception:
                fails += 1
                print(f"  !! {fn.__name__}({name!r}) in {root.name}")
                traceback.print_exc()
    for name in sorted(set(consts))[:PER_ENTRY]:
        checked += 1
        try:
            find_code_equations(sections, name)
        except Exception:
            fails += 1
            print(f"  !! find_code_equations({name!r}) in {root.name}")
            traceback.print_exc()
    return checked, fails, time.time() - t0


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    corpus = Path(sys.argv[1]).expanduser()
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 40

    # A STRIDE, not a prefix: `sorted(AFP)[:N]` is the entries whose names
    # start with A, which share authors, imports and style.
    all_entries = sorted(d for d in corpus.iterdir() if d.is_dir())
    step = max(1, len(all_entries) // cap)
    entries = all_entries[::step][:cap]
    total = failed = 0
    slowest: list[tuple[float, str]] = []
    for d in entries:
        checked, fails, dt = sweep(d)
        total += checked
        failed += fails
        if checked:
            slowest.append((dt, d.name))
            print(f"{d.name:40s} {checked:4d} scans  {dt:6.2f}s"
                  f"{'  FAIL' if fails else ''}")
    print(f"\n{total} scans over {len(entries)} entries, {failed} failures")
    for dt, n in sorted(slowest, reverse=True)[:5]:
        print(f"  slowest: {n} {dt:.2f}s")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
