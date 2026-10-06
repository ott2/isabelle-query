#!/usr/bin/env python3
r"""Probe: which shapes does a `lemmas` / `theorems` command take? [lemmas-entries]

Isabelle's grammar (Pure/Pure.thy, `theorems`/`lemmas`) is

    lemmas (in TARGET)? (thmdef? thms) and ... for_fixes?
    thmdef = NAME [attrs]? =        -- optional: `lemmas [simp] = foo` is anonymous

so one command may declare no name, one, or several.  Before deciding how the
command becomes an `Entry`, this counts each shape over the whole AFP + HOL +
FOL + ZF, in command position (`outer_source`), and prints samples of each.

Usage:  probe_lemmas_forms.py
"""
from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_query import cli  # noqa: E402

AFP = Path.home() / "repos" / "afp" / "thys"
DIST = Path("/Applications/Isabelle2025-2.app/src")

_CMD_RE = re.compile(r"^\s*(lemmas|theorems)(?![\w'])")
_NEXT_CMD_RE = re.compile(r"^\s*[a-z_]+(?![\w'.])")
_TARGET_RE = re.compile(r"^\s*\(\s*in\s+[\w'.]+\s*\)")
# A top-level `and` separates groups; brackets (attributes) are skipped.
_THMDEF_RE = re.compile(r"^\s*([\w'.]+|\"[^\"]*\")\s*(\[[^\]]*\])?\s*=(?!=)")
_ANON_DEF_RE = re.compile(r"^\s*(\[[^\]]*\])\s*=(?!=)")


def _groups(text: str) -> list[str]:
    """Split on `and` outside brackets."""
    out, depth, cur = [], 0, []
    toks = re.split(r"(\[|\]|(?<![\w'])and(?![\w']))", text)
    for t in toks:
        if t == "[":
            depth += 1
        elif t == "]":
            depth -= 1
        if t == "and" and depth == 0:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(t)
    out.append("".join(cur))
    return out


def main() -> None:
    paths: list[Path] = []
    if AFP.is_dir():
        for ent in sorted(d for d in AFP.iterdir() if d.is_dir()):
            paths.extend(sorted(ent.rglob("*.thy")))
    for sub in ("HOL", "FOL", "ZF"):
        if (DIST / sub).is_dir():
            paths.extend(sorted((DIST / sub).rglob("*.thy")))

    shapes: Counter[str] = Counter()
    names_per: Counter[int] = Counter()
    lines_per: Counter[int] = Counter()
    samples: dict[str, list[str]] = {}
    n_thy = 0
    for p in paths:
        try:
            sec = cli._parse_one(p.stem, p)
        except Exception:  # noqa: BLE001
            continue
        n_thy += 1
        outer = sec.outer_source()
        raw = sec.source()
        for i, line in enumerate(outer):
            m = _CMD_RE.match(line)
            if not m:
                continue
            # The command runs until a blank line or the next command.
            j = i + 1
            while j < len(outer) and outer[j].strip() \
                    and not _NEXT_CMD_RE.match(outer[j]):
                j += 1
            # Inner terms are blanked in `outer`; names and `=` survive.
            text =" ".join(outer[i][m.end():].split() +
                            [w for x in outer[i + 1:j] for w in x.split()])
            kind = m.group(1)
            tags = [kind]
            if _TARGET_RE.match(text):
                tags.append("in-target")
                text = text[_TARGET_RE.match(text).end():]
            if re.search(r"(?<![\w'])for(?![\w'])", text):
                tags.append("for")
            groups = _groups(text)
            named = sum(1 for g in groups if _THMDEF_RE.match(g))
            anon = sum(1 for g in groups if not _THMDEF_RE.match(g))
            if named == 0:
                shape = "anonymous"
            elif named == 1 and anon == 0:
                shape = "one name"
            elif anon == 0:
                shape = "several names"
            else:
                shape = "mixed named/anonymous"
            key = " ".join(tags) + ": " + shape
            shapes[key] += 1
            names_per[named] += 1
            lines_per[min(j - i, 6)] += 1
            if len(samples.setdefault(key, [])) < 3:
                samples[key].append(
                    f"{sec.theory}:{i + 1}  {raw[i].strip()[:70]}")

    print(f"=== {n_thy:,} theories, {sum(shapes.values()):,} commands ===\n")
    for key, n in shapes.most_common():
        print(f"  {key:<40} {n:>8,}")
    print("\nnamed groups per command:")
    for k in sorted(names_per):
        print(f"  {k:>3}  {names_per[k]:>8,}")
    print("\ncommand length in lines (6 = 6+):")
    for k in sorted(lines_per):
        print(f"  {k:>3}  {lines_per[k]:>8,}")
    print("\nsamples:")
    for key in sorted(samples, key=lambda k: -shapes[k]):
        for s in samples[key]:
            print(f"  [{key}]  {s}")


if __name__ == "__main__":
    main()
