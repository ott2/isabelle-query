# Proof-shape metrics — `query shape`

A command reference for the `shape` family. Where the other subcommands ask
*what is declared* and *which facts cite which*, `shape` measures the **shape of
individual proof steps**: how big a step is, how deeply nested, how many facts
it holds at once, how much it re-says, and how it is discharged.

Everything here is **source-level** — computed by parsing `.thy` text, with no
Isabelle build and no proof replay. Each value is either *exact* at source level
or a token-based *estimator*; estimator columns carry an `_est` suffix, so the
two are never silently conflated.

The authoritative definitions — each metric's exact rule, the term-level
semantics an estimator approximates, and its known approximations — are in
`src/isabelle_query/shape.py`, stated at the metric. This file decodes the
identifiers and says how to invoke them; it does not restate the definitions,
which would drift.

## Views

```sh
query shape summary                         # per-theory aggregate table
query shape steps [THEORY[:A..B]]           # per-step records
query shape lemma <name>...                 # one proof: every step + M6 curve
query shape widest [-N n] [PATH...]         # the widest steps
query shape census                          # stream per-proof JSONL over a corpus
```

| view | takes | output |
|---|---|---|
| `summary` | — | one row per theory |
| `steps` | an optional `THEORY` or `THEORY:A..B` span | one row per Isar step |
| `lemma` | one or more entry names | every step, an aggregate footer, and the M6 curve |
| `widest` | optional trailing `PATH`s | the *n* widest steps by a chosen metric |
| `census` | — | one JSON object per proof, streamed and resumable |

Flags, beyond the global `-R/--root` and `--version`:

| flag | views | meaning |
|---|---|---|
| `--json` | all but `census` | one JSONL record per line instead of the table |
| `-a`, `--all` | `steps` | include non-goal steps (context / plumbing / closing); the default shows goal steps only, where the metrics attach |
| `--scope {proof,entry}` | `summary` | size columns over the proof body (default) or the whole entry including its statement, as `largest` counts |
| `--content {all,code,prose}` | `summary` | size columns over all lines (default), code only (prose stripped), or prose only |
| `-N n` | `widest` | how many steps to rank |
| `--metric {w2,w1,fanin,live}` | `widest` | rank by as-written token width (default), free variables, cited facts, or simultaneously-live facts |
| `--config TOML`, `--corpus NAME` | `steps`, `lemma` | add the M3 `frame_ratio` columns; see [Corpus configs](#corpus-configs-m3) |
| `--resume FILE` | `census` | skip records already present in a prior run |

## Metrics

| id | column | measures | kind |
|----|--------|----------|------|
| M1 | `w1_est` | distinct free variables in the stated proposition | estimator |
| — | `const_est` | distinct constants in the stated proposition (names + operator notation) | estimator |
| — | `const_canon_est` | `const_est` with operator glyphs canonicalised to their Isabelle constant (`\<le>`/`\<subseteq>` → one) | estimator |
| M2 | `w2_src` | as-written proposition width, in tokens | exact |
| M3 | `frame_ratio` | delta-tracing overhead (components mentioned / changed) | definitional¹ |
| M4 | `dag_ratio_est` | cross-step redundancy (repeated bracketed subterms / block) | estimator |
| M5a | `fanin` | distinct facts cited for a step, by name or as a literal (`‹P›`, `` `P` ``) | exact |
| M5b | `live` | named facts simultaneously live at a step | exact |
| M5c | `introduce`/`consume` | fact-introducing vs fact-citing steps, a citation counted on the goal it serves | exact |
| M6 | extension curve | width remaining after naming the *k* most-repeated subterms | estimator |

¹ M3 is defined purely syntactically, so it has no estimator/reference split —
but it needs a per-corpus config.

The columns group into axes, which is how the `summary` table is laid out:

| axis | asks | columns |
|------|------|---------|
| Length | how big is the proof? | `n_steps`, `n_goals`, `n_bare` (+ `bare_kinds`), `proof_lines`, `proof_tokens` (raw + `_code`), `entry_lines` |
| Depth | how deeply nested? | `depth_max` |
| Width | how big is one step? | `w1_est`, `const_est`/`const_canon_est`, `w2_src` |
| Space | how many facts held at once? | `fanin`, `live`, `introduce`/`consume` |
| Redundancy | how much is re-said? | `dag_ratio_est`, M6 extension curve |
| Automation | how is it discharged? | `trivial_frac`, `method_kinds`, `methods`, induction discipline (`n_induct`, `induct_arbitrary_max`, `induct_recursion`) |
| Framing | how much to say to change a little? | `frame_ratio` |

They are separate measurements, not components of a single score: a proof can be
long and shallow, or short and wide.

`methods` counts how each method is applied, as `position:name/modifier`:
`by:simp/only` is not `by:simp`, and `apply:rule` is not `by:rule`. The
position is `by`, `apply`, `proof` or `qed` (`.` and `..` are forms of their
own); the name is the leading method, as `method_kinds` reads it; the
modifier is the first `word:` inside it, the keyword and never its argument.
`method_kinds` is the `by:` / `apply:` forms bucketed by name.

**Every proof is measured**, not only the proofs of facts: an `instance`,
`sublocale`, `interpretation`, `termination`, `typedef`, `notepad` and every
other built-in command with a goal kind carries a proof, and gets a record of
its own. `tag` says what owns the proof (`LEMMA`, `INSTANCE`, ...) and `line`
where; `(theory, line)` is a record's key. Over the AFP these are 5.5% of
proofs and 3.7% of proof code, `sublocale` and `interpretation` most of it.

A **step is an Isar command**: `have a: "P" using q by simp` is three steps,
whether on one line or three. Only `proof_lines` and `entry_lines` see the
layout; every other column is the same however the proof is broken into lines.
`proof`, `next`, `{` and `}` are structure, not steps, and `also` / `finally`
are plumbing (Isabelle's `prf_decl` / `prf_chain`), not goals.

## JSONL records

Every record carries `schema`, the version of the definitions its numbers
follow. It changes when a field's meaning does, so records with different
`schema` values do not compare, even where their keys match. 1.1.0 writes `2`;
earlier records have no `schema` and follow `1`.

`--json` (and `census`) emit one JSON object per line, keyed by a stable
`(theory, lemma)` position, plus `(line, col)` for a step, so records join
across runs without re-instrumentation. Two record shapes — per-step (`steps` / `lemma` / `widest`)
and per-proof aggregate (`summary --json` / `census`). **The full field lists are
in the `shape_cmds` module docstring.**

Per-proof records also carry `session` (`null` when the load had no session
context), which a corpus run needs: AFP theory names are not unique across
entries, so `(theory, lemma)` alone cannot identify one.

`n_bare` counts goal steps with no as-written proposition — excluded from the
width distributions, because there is nothing to measure — and `bare_kinds`
says **why**, in three keys that sum to it:

| key | meaning | whole AFP |
|---|---|---|
| `construction` | the step cannot state one: `show ?thesis`, `thus ?case`, `also`, `interpret` | 94.64% |
| `undelimited` | written on the line without quotes or a cartouche (`hence False by simp`) | 5.09% |
| `unfound` | the scanner looked and found nothing — mostly `consider` with its case names (`(a) "P"`) on the next line | 0.26% |

The split is what makes a change in `n_bare` readable: `construction` moves
with writing style, `unfound` with this scanner. Pooled, a rise could be either,
which is how a wrapped-statement bug once hid inside it. `n_bare` itself is
unchanged, so rows from before the split still compare.

## Running a census over a corpus

```sh
query -R AFP/thys shape census > afp.jsonl
```

One process for the whole corpus, one session at a time — do not loop `query`
over entries in a shell, which pays interpreter and process startup per entry
and dominates the run. Memory is bounded by the largest single session rather
than by the corpus, and a session that fails to parse is reported on stderr and
skipped rather than aborting the run.

Output is flushed per session, so a killed run leaves a valid JSONL prefix, and
`--resume FILE` skips records already present:

```sh
query -R AFP/thys shape census --resume afp.jsonl >> afp.jsonl
```

Exit status follows the usual rule: `2` if no session could be read at all,
`0` with a stderr summary if some were skipped, `0` in silence for an honest
zero. A directory with no `ROOT` is still a corpus (the `*.thy` fallback),
censused as a single unnamed group.

## The method table, and what it still decides

The one place Isabelle informs a result is the method/attribute table that tells
a proof method (`by auto`) from a fact citation. It used to bound the shape
numbers as well; it no longer does, and the distinction is the subject of this
section.

`census` uses a fixed, committed **approximate** table — the union of the
distribution sessions most AFP entries build on (HOL, HOL-Library, HOL-Analysis,
HOL-Eisbach, HOL-Decision_Procs) — so it needs no Isabelle and regenerates
identically anywhere. Being fixed, it is an approximation: methods an entry
defines itself (an Eisbach `cs_concl`) or that come from a niche logic (Nominal's
`nominal_induct`) are not in it.

**No shape axis depends on it, though.** That includes the **Automation** axis,
which used to: `Step.method` is whatever stands in *introducer position* after
`by` / `apply` / `proof`, where the token is the method by construction and a
table filters nothing. So `trivial_frac` and `method_kinds` are positional like
fan-in, width and depth, and binding a different table cannot move a shape
record. An entry's own tactic lands in `method_kinds.other` rather than
disappearing — which is why `other` means "outside the four core families", not
"recognised but outside them".

Where the table's absence *would* have shown is worth stating, because it is the
reason this changed: a method the table lacked left `Step.method` empty, and that
is `trivial_frac`'s denominator, so the proof reported `None` — "discharges
nothing" — rather than a wrong number. Corpus-wide that silently mislabelled
1.29% of AFP proofs, concentrated by style rather than spread as noise:
`Auto2_Imperative_HOL` reported `None` for 305 of its 349 proofs, because
`auto2` is its own tactic. It is now 0.

The per-project verbs (`callers` / `callees` / `unused` / `methods` / `shape`)
instead resolve a **session-exact** table from a loaded Isabelle heap when one is
built — cached, and never a build. Heaps are looked for where Isabelle looks:
`$ISABELLE_HEAPS` first, then `$ISABELLE_HEAPS_SYSTEM`, so a stock install with
nothing built locally still resolves the exact table from the distribution's own
`HOL`. With no heap, a HOL-base project falls back to the same broad table
`census` uses, so the two agree; only a positively non-HOL project (`ZF`, `FOL`)
is stepped down to the minimal Pure core, and that case is **warned** on stderr.

So what the table still decides is **not** the shape numbers but two other
things:

- **Method or citation?** A token in the table is not read as a fact name, which
  is what keeps `by (simp add: foo)` from edging the call graph to `simp`. This is
  position-blind — a method name can appear as a bare argument — so a table is the
  right instrument, and a *narrow* one is the safe direction: an unlisted method
  may add a spurious citation, never remove a true one.
- **Constant or variable?** `const_est` and its kin ask whether an identifier in a
  proposition is syntax; `auto` reads as a constant under the broad table and as a
  free variable under the Pure floor.

**Using the package as a library.** Importing the package binds the broad
committed table, the same one `census` uses, so a direct caller that configures
nothing agrees with a census — and since the automation axis is positional, the
axis agrees even if the binding is wrong. Two reasons to change it: call
`graph.use_pure_namespace()` for a non-HOL project, or
`graph.configure_namespace(methods, attributes, keywords)` to install a
session-exact table you resolved yourself.

A second, smaller committed table backs `const_canon_est`: a notation table
mapping operator glyphs to their Isabelle constant (`\<le>` → `less_eq`),
resolved once from a heap by `scripts/extract_notation.py` and checked in, so
runtime stays pure-Python. A glyph the table does not carry falls back to itself,
so it only ever dedups, never loses, a constant — and the raw-glyph `const_est`
beside it stays table-independent.

## Corpus configs (M3)

Source parsing cannot resolve types, so M3's "configuration type" degrades to a
per-corpus list of selector / constructor / relation names. Supply it as TOML —
one `[corpus]` table per entry — and pass `--config FILE [--corpus NAME]` to
`steps` / `lemma` to add the `frame_ratio` columns. `configs/m3.toml` ships a
`Cook_Levin` table. Without a config the rest of the family runs unchanged.

When comparing across corpora, normalize per proof or per goal step, never per
kloc — line counts confound formatting.
