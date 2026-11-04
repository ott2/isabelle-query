#!/usr/bin/env python3
r"""How common are the name-bearing document antiquotations, and what would
reading them cost (#44)?

For each kind (`const`, `term`, `typ`, `type`, `thm`) in both spellings
(`@{term "..."}`, `\<^term>\<open>...\<close>`), counts:

* occurrences, and how many have a body spanning more than one line;
* `@{...}` bodies holding a `}` inside a string or cartouche, where a
  `[^}]*` body regex (what `graph._AT_ANTIQ_RE` uses for `thm`) stops early;
* for `term`, how many bodies name an entry the same session declares,
  and how many (session, name) pairs only a `term` body contributes, beyond
  what the bare-name kinds already give.

It also times this scan against `graph.doc_mentions`, the scan `unused`
runs today, over the same parsed sections.

    python scripts/probe_antiquotations.py [ROOT] [--limit=N] [--show=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import re
import sys
import time
from collections import Counter
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import graph
from isabelle_query.parsing import sections_for_session

KINDS = ("const", "term", "typ", "type", "thm")
_START = re.compile(r"@\{\s*(const|term|typ|type|thm)\b"
                    r"|\\<\^(const|term|typ|type|thm)>\s*(?=\\<open>|‹)")
_OPEN, _CLOSE = ("\\<open>", "‹"), ("\\<close>", "›")
_SYMBOL = re.compile(r"\\<[^>]*>")
_NAME = re.compile(r"[A-Za-z][\w'.]*")


def _cartouche_end(text: str, i: int) -> int:
    """Index just past the cartouche opening at `i`, nesting counted."""
    depth = 0
    while i < len(text):
        for o in _OPEN:
            if text.startswith(o, i):
                depth += 1
                i += len(o)
                break
        else:
            for c in _CLOSE:
                if text.startswith(c, i):
                    depth -= 1
                    i += len(c)
                    if depth == 0:
                        return i
                    break
            else:
                i += 1
    return len(text)


def _at_end(text: str, i: int) -> tuple[int, bool]:
    """Index just past the `}` closing an `@{` body that starts at `i`, and
    whether a `}` occurred inside a string or cartouche on the way."""
    inner_brace = False
    while i < len(text):
        ch = text[i]
        if ch == "}":
            return i + 1, inner_brace
        if ch == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" and text[j + 1:j + 2] == '"' else 1
            inner_brace |= "}" in text[i:j]
            i = j + 1
        elif any(text.startswith(o, i) for o in _OPEN):
            j = _cartouche_end(text, i)
            inner_brace |= "}" in text[i:j]
            i = j
        else:
            i += 1
    return len(text), inner_brace


def scan(text: str):
    """Yield (kind, spelling, body, inner_brace) per antiquotation."""
    for m in _START.finditer(text):
        if m.group(1):
            end, inner = _at_end(text, m.end())
            yield m.group(1), "@{}", text[m.end():end - 1], inner
        else:
            end = _cartouche_end(text, m.end())
            yield m.group(2), "\\<^>", text[m.end():end], False


def names_in(body: str) -> set[str]:
    return {n.rsplit(".", 1)[-1] for n in _NAME.findall(_SYMBOL.sub(" ", body))}


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp-devel" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 10))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    count, multi, brace = Counter(), Counter(), Counter()
    term_bodies = term_hits = 0
    bare_pairs: set = set()
    term_pairs: set = set()
    samples: list[str] = []
    t_doc = t_scan = 0.0
    n_thy = 0
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        n_thy += len(secs)
        declared = {e.name for s in secs for e in s.entries if e.name != "?"}
        t0 = time.perf_counter()
        graph.doc_mentions(secs)
        t_doc += time.perf_counter() - t0
        t0 = time.perf_counter()
        found = [(sec, a) for sec in secs
                 for a in scan("\n".join(sec.source()))]
        for _sec, (kind, _sp, body, _inner) in found:
            hits = names_in(body) & declared
        t_scan += time.perf_counter() - t0
        for sec, (kind, sp, body, inner) in found:
            key = (kind, sp)
            count[key] += 1
            if "\n" in body:
                multi[key] += 1
                if kind == "term" and len(samples) < show:
                    samples.append(f"{sec.path.name}: {' '.join(body.split())[:90]}")
            if inner:
                brace[key] += 1
            hits = names_in(body) & declared
            pairs = {(session.name, n) for n in hits}
            if kind == "term":
                term_bodies += 1
                term_hits += bool(hits)
                term_pairs |= pairs
            elif kind in ("const", "typ", "type"):
                bare_pairs |= pairs
    print(f"{n_thy:,} theories\n")
    print(f"{'kind':6} {'spelling':8} {'count':>8} {'multi-line':>11} "
          f"{'} inside':>9}")
    for kind in KINDS:
        for sp in ("@{}", "\\<^>"):
            k = (kind, sp)
            print(f"{kind:6} {sp:8} {count[k]:8,} {multi[k]:11,} "
                  f"{brace[k]:9,}")
    print(f"\nterm bodies naming a same-session entry: {term_hits:,} of "
          f"{term_bodies:,}")
    print(f"(session, entry) pairs from const/typ/type: {len(bare_pairs):,}; "
          f"from term only: {len(term_pairs - bare_pairs):,}")
    print(f"\ntime: doc_mentions {t_doc:.2f}s, this scan {t_scan:.2f}s")
    if samples:
        print("\nmulti-line term bodies:")
        for s in samples:
            print(f"  {s}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
