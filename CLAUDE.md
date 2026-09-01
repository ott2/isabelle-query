# CLAUDE.md — orientation for isabelle-query

This is the every-session story: what `query` is, how it is laid out, and where
everything else is written down. It is deliberately short. Granular working
rules live in `.claude/memory/` (auto-loaded); the current session's in-flight
state lives in the gitignored `prompt.md` handoff.

## What query is

`query` is a fast, syntax-aware, **pure-Python** command-line tool for querying
an Isabelle/Isar project. It parses the project's `.thy` sources on every
invocation — **no Isabelle build, no proof replay** — so results always match
the current tree, and even the whole AFP parses in ~1–2 minutes. (The one
Isabelle touch-point is the method/attribute *table* the table verbs use to tell
a proof method from a citation: resolved once from a loaded heap and cached, or
the committed table when Isabelle is absent — never a build; see
[[reuse-infrastructure-not-reinvent]].) It answers three kinds of question:

- **Structure** — *what is declared, and where*: `summary`, `theory`, `find`,
  `show`, `largest`, `outline`, and its inverse `enclosing` (which also names
  the enclosing locale/class target).
- **Usage** — *which facts cite which*: `callers`, `callees`, `deps`, `refs`,
  `unused` (built on a call graph constructed only when needed). `deps`/`uses`
  read the `imports` clause; `refs` rolls the *citation* graph up by theory, so
  the two disagreeing is the signal (an import nothing cites, or the converse).
- **Shape** — *the proof-complexity shape of individual steps*: `query shape`
  (a nested view family — `summary`/`steps`/`lemma`/`widest`/`census`).

`query -h` lists all subcommands; each takes `-h`. Locations and spans share one
grammar (`theory:line`, `theory:A..B`), so the tool's output is valid input.

## Architecture

The package is a strict module DAG — each imports only from earlier links:

    model → parsing → graph → render → commands → cli

with `shape` + `shape_cmds` (the proof-shape family), `_prog` (the invoked
command name — a leaf that imports nothing, so any layer can reach it), `api`
(the four-name supported import surface, sitting just above `parsing` and
importing nothing else — see `CONTRIBUTING.md`), and `scripts/` (offline
table-generation + dev utilities) as siblings.

Session/ROOT discovery and the import closure are **not query's code**: the
ROOT / session / theory-header parser is **`isabelle-layout`** (on PyPI,
query's one runtime dependency), imported directly at each call site.  There is
no `common.py` — it was a re-export shim for callers written before the split,
and retiring it is the breaking half of 0.7.0. The dependency is deliberately
uncapped: `tests/test_layout_surface.py` pins the ten names query reaches for,
**all of them public**, and fails on any private import anywhere in the repo.
That is what a version range was standing in for.

- `model` — dataclasses (`Entry`, `TheorySection`, `CallGraph`), plus the two
  redacted views every scanner reads: `live_source()` (noise blanked, terms
  kept — a citation scan must see `mono` in `lemma "mono f"`) and
  `outer_source()` (terms blanked too — command position, which is where a
  declaration may start).
- `parsing` — `.thy` → entry DB; the `_sections_from_dir` loader.  One
  tokenizer pass (`scan_regions`) feeds all of it: noise spans, genuine
  `\<comment>` starts, inner-syntax spans, and `open_at` (did this line begin
  mid-term).  Nothing in the grammar uses indentation as evidence.  Block
  structure comes from the `begin`/`end` pair every target block shares
  (`_block_stacks`), which is what gives an entry its `blocks` / `in_target`.
- `graph` — usage analysis + the shared step-scanner primitives.
- `render` / `commands` / `cli` — formatting, the `cmd_*` handlers, the argparse
  facade (which re-exports lower-layer names so tests reach `cli.X`).
- `shape` — the per-step shape engine; `shape_cmds` — its CLI verbs.

**Discovery loads what `isabelle build` compiles:** each session's ROOT-declared
theories *plus the transitive closure of their in-entry `imports`* (via
`isabelle_layout.session_theories`). Imports of *other* AFP entries and
of the base library (`HOL-*`, `Pure`) are not followed; orphan `.thy` files are
excluded.

## The document map

| doc | what |
|---|---|
| `README.md` | user-facing entry point: what the tool is, the subcommands, examples, install. Kept **short** — it is the GitHub landing page |
| `SCANNING.md` | user-facing: how a project is read — live-text scanning, locale scope, method-vs-fact names, session discovery, the prose view |
| `METRICS.md` | user-facing: the `query shape` **command reference** and the `M1`–`M6` table. Deliberately not motivation — the research framing for these metrics lives outside this repo |
| `CONTRIBUTING.md` | **normative**: the CLI contract, and where design decisions are recorded |
| `todo.md` | **open work only** — not a changelog; completed work lives in its commit messages |
| `src/isabelle_query/shape.py` | **authoritative** metric definitions and approximations |
| `.claude/memory/` | granular working rules + project facts (auto-loaded index) |
| `prompt.md` | **gitignored** end-of-session handoff (survives compaction; not the design) |

Design decisions are recorded **in commit messages**, cross-referenced by a
stable `[tag]`: `git log --grep='\[locus-roundtrip\]'`.  There is no changelog
and no design-decision archive — a summary of a commit drifts from it, and the
commit does not.

## Working essentials

The full rules are in `.claude/memory/` — start from `MEMORY.md`. The few that
matter every session:

- **Environment.** The `.venv` is already active (Python 3.14). Run `pytest` /
  `query` / `pip` **by bare name**; do **not** `cd` into the working dir (it
  trips the permission gate). `ruff` is not installed.
- **Corpora.** AFP checkout: `~/repos/afp/thys` (Isabelle2025-2); enumerate a
  corpus's sessions via `isabelle_layout.iter_sessions`, never a bare `rglob`.
- **Correctness.** Verify against Isabelle semantics, not prior behavior;
  hand-compute a fixture value first, then make the code match. `pytest -q` stays
  green after every change.
- **Commits.** Small, single-concern, frequent — commit often, don't push unless
  asked. Trailer, verbatim:
  `Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>`.
  Write commit bodies to a `.commit-msg` scratch file in the working tree (not
  `/tmp`, which is gated); `rm` it after.
- **Reuse over re-roll.** Corpus/tooling scans reuse `cli._parse_one` +
  `shape`'s primitives; don't write a second parser.

## Release status

The released version tracks `pyproject.toml` (currently **0.8.1**). Versioning is
alpha, and 0.7.0 is where the policy tightened: a **breaking change now takes
the minor slot** (0.x semver — 0.6.x → 0.7.0), rather than riding a patch bump
as it did while the CLI was moving weekly. Patch bumps stay additive. Switch to
major-for-breaking once the CLI settles.

There is no changelog, by the same reasoning that keeps design decisions in
commit messages. **Release notes are the version-bump commit's message**, and
that is load-bearing rather than a convention: `make release` tags HEAD with a
bare label, and `.github/workflows/release.yml` publishes the *tagged commit's*
message as the GitHub Release body. Notes written into the tag annotation are
silently dropped. Write them in the bump commit, then `make release`.

`make release` now **builds before it tags** — guards (clean tree, tag not
taken) first, then `python -m build`, then the tag and push — so a broken build
costs nothing while a pushed tag cannot be taken back. `make dist` does the
build alone.

Artifacts go in **`dist/`**: plain `python -m build`, no `--outdir`, since that
is the default and it is gitignored. `build` does **not** clean it, so every
past release accumulates there — which is why the upload command is
**version-scoped** and `make release` prints it as its last line:

    twine upload -r pypi-isabelle-query dist/isabelle_query-<version>*

A bare `dist/*` would re-offer already-published releases. The **user** uploads
to PyPI, not the assistant: it is the one step here that cannot be undone.

## Credit

**Published artifacts** carry the line "By András Salamon, with Claude Opus
4.6, 4.7, 4.8, and 5." — `README.md`'s sign-off and `pyproject.toml`'s author
comment are the two places it belongs.

**Commit messages do not.** They carry the `Co-Authored-By` trailer alone, and
that includes the version-bump commit — even though its message is published
verbatim as the GitHub Release body, a commit is not an artifact for this
purpose. v0.7.0 carried both and is the only one of the eight releases that
did; v0.6.3–v0.6.8 and v0.8.0 are the pattern.
