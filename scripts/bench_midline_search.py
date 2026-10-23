#!/usr/bin/env python3
"""Compare ways to find mid-line declaring keywords [midline-decl].

`parsing._mid_decls` uses the prefix-factored alternation (`trie_only`).  All variants run on
the same outer views in one process, so a busy machine slows them alike;
compare the ratios, not the seconds.

    python scripts/bench_midline_search.py FILE.thy [...]
"""

import re
import sys
import time
from pathlib import Path

from isabelle_query import parsing

WORDS = parsing._DECL_WORDS


def by_mid_decls(texts):
    return sum(len(parsing._mid_decls(o)) for o, _t in texts)


BARE_RE = re.compile(rf"(?:{WORDS})")
_BEFORE = frozenset(" \t)]}")


def by_bare_regex(texts):
    n = 0
    for _o, t in texts:
        for m in BARE_RE.finditer(t):
            k, end = m.span()
            if k and t[k - 1] in _BEFORE and (
                    end == len(t) or t[end].isspace()):
                n += 1
    return n


BARE_BRE = re.compile(rf"(?:{WORDS})".encode())
LEAD_BRE = re.compile(rf"[ \t)\]}}](?:{WORDS})(?=\s|$)".encode())


def by_bytes_bare(texts):
    n = 0
    for _o, t in texts:
        b = t.encode()
        for m in BARE_BRE.finditer(b):
            k, end = m.span()
            if k and b[k - 1] in b" \t)]}" and (
                    end == len(b) or b[end:end + 1].isspace()):
                n += 1
    return n


def by_bytes_lead(texts):
    return sum(sum(1 for _ in LEAD_BRE.finditer(t.encode()))
               for _o, t in texts)


BWORDS = [w.encode() for w in WORDS.split("|")]


def by_bytes(texts):
    n = 0
    for _o, t in texts:
        b = t.encode()
        for kw in BWORDS:
            k = b.find(kw)
            while k >= 0:
                end = k + len(kw)
                if k and b[k - 1] in b" \t)]}" and (
                        end == len(b) or b[end:end + 1].isspace()):
                    n += 1
                k = b.find(kw, end)
    return n


def join_only(texts):
    return sum(len("\n".join(o)) for o, _t in texts)


def finditer_only(texts):
    return sum(sum(1 for _ in BARE_RE.finditer(t)) for _o, t in texts)


TRIE_RE = parsing._DECL_WORD_RE      # factored by prefix


def trie_only(texts):
    return sum(sum(1 for _ in TRIE_RE.finditer(t)) for _o, t in texts)


def main() -> int:
    texts = []
    for arg in sys.argv[1:]:
        p = Path(arg)
        o = parsing._parse_one(p.stem, p).outer_source()
        texts.append((o, "\n".join(o)))
    for fn in (by_mid_decls, join_only, finditer_only, trie_only):
        t0 = time.perf_counter()
        n = fn(texts)
        print(f"{fn.__name__:14} {time.perf_counter() - t0:.3f}s  {n} hits")
    return 0


if __name__ == "__main__":
    sys.exit(main())
