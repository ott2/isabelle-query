# isabelle-query

`query` is a command-line tool for **querying an Isabelle/Isar project** — its
entries (definitions, lemmas, theorems, datatypes), call graph, theory
dependencies, outstanding `sorry`s, dead code, and the shape of its proofs.

It parses the project's `.thy` sources on every invocation, so results always
match the current tree: **no Isabelle build, no proof replay**. A large project
parses in a fraction of a second, and the whole AFP in a couple of minutes. It is
aimed at projects big enough that grep-and-examine has stopped working — AFP
entries, the AFP itself, or industrial verification.

Pure Python. One runtime dependency,
[isabelle-layout](https://pypi.org/project/isabelle-layout/) — the ROOT and
theory-header parser, split out so that reading an Isabelle project's structure
does not require installing a CLI. `pip` fetches it for you.

News 2026-08-29: David Wang has [ported isabelle-query to Scala](https://github.com/david-wang-0/isabelle-query)
which of course unlocks a bunch of new features since that improves integration
with Isabelle.

## Commands

```sh
query summary              # theory overview table (-S: corpus/session aggregate)
query theory MyTheory      # entries in a theory (-n for terse names)
query find <regex>         # search entry names (--statement: search statements; --and: all patterns)
query show <name>          # a named entry's declaration + body
query enclosing FILE:LINE  # which entry + proof block owns a line; inverse of outline
query callers <name> [-r]  # who references a name  (reverse; -r = transitive)
query callees <name> [-r]  # what a name references (forward)
query deps <theory> [-r]   # what a theory imports  (forward; reverse: uses)
query refs <theory>        # what a theory cites, by owning theory (citation-level)
query graph [citation|imports]  # the whole graph as JSON (-f dot for Graphviz)
query sorry                # outstanding sorry's
query unused               # dead-code / unused-entry analysis
query instances <name> [-r]  # where a locale/class is instantiated; -r walks the hierarchy
query codeqs <name>        # declared code-equation sites of a constant
query shape <view>         # proof-shape metrics (summary|steps|lemma|widest|census)
```

Every subcommand takes `-h`; `query -h` lists all 22.

## Examples

Point `query` at any session directory with `-R` (or `--root`):

```sh
query -R AFP/thys largest                          # the biggest entries, by line count
query -R AFP/thys callers metric_domain_tfin_def   # every proof step that cites a fact
query -R AFP/thys find --statement tfin            # lemmas *stated about* tfin, whatever their name
query -R AFP/thys find --statement --and length tfin  # ...and mentioning length too (--and intersects)
query -R AFP/thys enclosing Tfin.thy:412           # the lemma and nearest proof block a build error sits in
query -R AFP/thys enclosing Tfin:88..140           # every entry a diff hunk touches
query -R AFP/thys grep simp Tfin.thy:88..140       # search just a hunk
```

Locations and spans share one grammar (`theory:line`, `theory:A..B`), so the
tool's output is valid input: a locus from `callers` / `sorry` pastes into
`enclosing`, and a span from `outline` / `largest` — or a proof block from
`enclosing`'s own drill-down (`▸ have key 11..14`) — pastes into `lines`.

A theory prints as its bare name, and only far enough qualified to name one
theory. Over a corpus that matters: nineteen AFP theories are called
`Examples`, so `largest` reports `Virtual_Substitution/QE` and `enclosing`
takes it straight back. A name used once stays bare.

## What it reads

Only **live Isar text**. A name in a comment, a `\<comment>` note, a `text`
block or an `ML` body is not a citation, so it never invents a caller or hides a
dead lemma — and a `definition` left behind in a comment is not an entry.
Regions are found by a character-level scan, not by line, so
`by (simp add: foo) (* not bar *)` keeps `foo` and drops `bar`.

Layout carries no meaning: Isar is whitespace-insensitive, so a declaration is
recognised wherever a *command* can start, at any indentation and any block
depth. Discovery loads what `isabelle build` compiles — each session's declared
theories plus the closure of their in-entry imports.

See **[SCANNING.md](SCANNING.md)** for the details: locale scope, method names
that collide with fact names, corpus aggregation, and the prose view.

### Instantiation and code-equation sites

`instances` and `codeqs` report **declared source sites**, not the processed
setup a prover's `print_interps` / `print_codesetup` shows. Rows have the form
`LOCUS NAME KIND source`; a site whose source writes no name shows `?`.
`--sorts` adds only the sort, arity or signature written at the site, never an
inferred type.

`instances -r` also lists the sites of everything that **extends** the subject —
`class X = NAME + …`, `locale X = … NAME …`, `subclass`, `instance X ⊆ NAME`,
`sublocale` — transitively, and adds a `VIA` column naming which of them each
row writes. `nat` instantiates `comm_monoid_diff`, never `ab_semigroup_add` by
name, so it appears only under `-r`. Without the flag the listing is the direct
sites alone.

**`codeqs` under-reports when mixfix notation hides the statement's head
symbol.** Check source with `grep` if an answer looks short. Neither verb
separates same-named declarations that are both visible from one theory: a
site is attributed to a declaration in that theory or its transitive imports
within the scanned project, and declarations that live only in a heap are not
discovered.

## Proof-shape metrics

`query shape` measures the shape of individual proof steps — how big a step is,
how deeply nested, how many facts it holds at once, how much is re-said, and how
it is discharged. All source-level, no build.

```sh
query shape summary                  # per-theory aggregate table
query shape lemma <name>             # one proof: every step
query -R AFP/thys shape census       # per-proof JSONL over a whole corpus
```

See **[METRICS.md](METRICS.md)** for the command reference, the metric table, and
the JSONL record schema.

## Exit status

`0` the command ran; `1` the request could not be resolved (unknown theory,
entry name or path, no subcommand); `2` bad usage — an argparse error, or **a
root that could not be read**; `141` a write failed because a downstream reader
closed the pipe (`query shape census | head` over a corpus), as a shell reports
for SIGPIPE.

**A diagnostic goes to stderr and stdout stays clean**, so a count mode is
always safe to capture. The two empty answers are different and say so:

```
$ query find zzz -c        # a real search that found nothing
0
$ echo $?
0
$ query callees zzz -c     # there is no entry `zzz` to have callees
query: 'zzz' is not in the entry index
$ echo $?
1
```

`instances` and `codeqs` exit `1` for a subject that is not a declared locale
or class, respectively constant — a typo and a locale from an imported session
would otherwise look exactly like one nobody instantiates — and `0` for a
declared subject with no sites.

`141` is not promised for *every* `| head`. When the whole answer fits the pipe
buffer no write ever fails and the status is `0` — the same as `seq 10 | head`,
where `seq 200000 | head` dies of SIGPIPE. The producer wrote everything; the
reader chose to stop. Either way stderr stays silent and the status is
deterministic.

A root that yields no theories is reported on stderr and never as an empty
success, so a script can tell a broken run from an honestly empty one:

```
$ query -R /typo/path shape census
query: /typo/path: no such directory (given to -R/--root)
$ echo $?
2
```

## Library API

The Isar span parsing is importable, for tools that want **spans** rather than
a **report** — where a lemma starts and ends, where its `text ‹…›` preamble is,
where its proof stops, which lines are comments or ML.

```python
from pathlib import Path
from isabelle_query.api import parse_root, parse_theory

sec = parse_theory("Foo", Path("Foo.thy"))
for e in sec.entries:
    print(e.name, e.src_start, e.thy_end, e.proof_line, e.body_end_line)
```

`isabelle_query.api` exports exactly four names — `parse_theory`, `parse_root`,
`Entry`, `TheorySection` — and **they follow the same policy as the CLI: a
change that breaks them takes the minor version slot, never a patch.** Nothing
else in the package is supported; import from `isabelle_query.parsing` and a
patch release may move it.

Four rather than the dozen functions that look public, because their results
are already fields on the two objects, and the hard part is the order the
scanners run in — that composition is what `parse_theory` is. Use `parse_root`
whenever the answer must match `query -R`: Isabelle's keyword table is
session-wide, so a single theory parsed alone cannot see a custom command a
sibling declares.

## Installation

Requires Python 3.9 or greater. Installs the command on your `PATH` under two
names — **`query`**, the short form used throughout these docs, and
**`isabelle-query`**, matching the distribution — and pulls `isabelle-layout`
from PyPI. They are the same program, and it reports whichever you typed, so
`isabelle-query -h` documents `isabelle-query`.

```sh
pip install isabelle-query     # from PyPI
pip install .                  # from a checkout
```

An editable install, for working on the tool itself:

```sh
git clone https://github.com/ott2/isabelle-query
cd isabelle-query
python -m venv .venv && source .venv/bin/activate   # optional but recommended
pip install -e .
```

## Documentation

| file | what |
|---|---|
| [SCANNING.md](SCANNING.md) | how `query` reads a project — what counts as a declaration, a citation, and a session |
| [METRICS.md](METRICS.md) | `query shape` command reference and metric definitions |
| [CONTRIBUTING.md](CONTRIBUTING.md) | the CLI contract and where design decisions are recorded |

## Authors & license

By András Salamon, with Claude Opus 4.6, 4.7, 4.8, and 5. [MIT](LICENSE).
