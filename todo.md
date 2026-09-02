# Todo list

**Open work only.** Ordered by priority (highest first).  Tags are stable
handles for cross-referencing in commits/PRs — and, once an item ships, for
finding it again with `git log --grep`.

Conventions for changing the tool (the CLI contract, verification habits) live
in `CONTRIBUTING.md`.

- [ ] `[oracle-drop-rate]` The corpus call-graph test is **RED**:
      `test_fast_call_graph_matches_oracle_on_subset` reports the fast builder
      dropping **505 of 10,898** caller-edges against the brute-force reference,
      where `_MAX_DROP_FRACTION = 0.005` allows 54.
      Reproduced on `6168b9e` (v0.8.1 + docs) as well as on HEAD, so it predates
      the `[markup-step-model]` work and is not that change.  The run also takes
      ~110s where the handoff recorded ~23s, which points at the AFP checkout
      having moved under the 120-file subset rather than at a code change — but
      that is a hypothesis, not a measurement.  Establish which before touching
      the ceiling: a threshold raised to make a test green is worthless, and the
      test exists precisely because the fast builder must not silently diverge.
      `ISABELLE_QUERY_CORPUS=~/repos/afp/thys pytest -q tests/test_corpus.py`

- [ ] `[decl-commands]` Four fact-declaring commands are **not declarations**,
      so `query` cannot see them and — worse — they do not bound the previous
      entry either, so the lemma above them swallows their proof.  `DECL_RE`
      lists `lemma|corollary|theorem` and stops.
      Measured over 2,644 theories (60 AFP entries + all of HOL/FOL/ZF) by
      `scripts/probe_missing_decl_commands.py`, command position only:

          lemmas            3,491      proposition        601
          named_theorems      207      schematic_goal     160
          private lemma       275      qualified lemma    209   (+~250 modified)

      **`proposition` is the clear one**: Isabelle declares it `thy_goal_stmt`
      in `Pure`, the identical kind to `lemma` / `theorem` / `corollary`, three
      of which `DECL_RE` already knows.  There is no design note excluding it —
      the table's only deliberate absences are `context` and `interpretation`,
      which reopen or instantiate rather than declare.
      The knock-on is what makes it worth doing rather than tidy:
      `probe_proof_bearing_commands.py` reads `proposition` as 34.3% unscanned
      rather than 100%, because two thirds of the time the preceding lemma's
      span has already reached over it and its steps were counted as that
      lemma's.  So this moves the entry set AND the census, and the fix must
      report both.
      `private` / `qualified` are a different shape: namespace MODIFIERS that
      may precede any declaration, so the fix is a prefix skip, not four more
      table rows.  `lemmas` / `named_theorems` declare a citable fact with no
      proof (they touch `find` / `show` / `callers`, not `shape`);
      `schematic_goal` has one.  Worth splitting if they do not share a change.

- [ ] `[proof-bearing-commands]` **(scope call, not a defect.)**  A command that
      proves something but declares no fact — `instance`, `sublocale`,
      `interpretation`, `subclass`, `termination`, `notepad` — is not an
      `Entry`, has no `proof_line`, and its proof is invisible to every `shape`
      verb.  Measured by `scripts/probe_proof_bearing_commands.py` over 687
      theories: **11,300 proof commands, ~2% of the corpus**, 100% unscanned
      for each of these owners.

          interpretation dual: abstract_boolean_algebra ...  HOL/Boolean_Algebras:140
            apply standard                     <- five proof commands,
                 apply (rule disj_conj_distrib)    none of them measured
                apply (rule conj_disj_distrib)
               apply simp_all
            done

          instance                6,706   sublocale         1,444
          subclass                  707   lift_definition     577
          global_interpretation     574   interpretation      752
          termination               194   notepad             160

      The question is whether `shape` measures *proofs* or *proofs of facts*.
      Today it is the second, by accident rather than by decision — the entry
      model is a **declaration** index and `shape` rides on it.  Both readings
      are defensible and the numbers differ by ~2%, so the answer belongs in a
      commit message before any code moves.  Note `instance` alone is 6,706 and
      is mostly one-liners (`instance ..`), so the population is not shaped
      like the lemma population and would move the aggregate distributions, not
      just their totals.  Distinct from `[decl-commands]`, which is a defect in
      the same probe's other half.

- [ ] `[comment-newline]` A `\<comment>` may be separated from its cartouche
      by a newline.  Isabelle's `comment_prefix` allows any blanks between the
      marker and the cartouche it owns, newlines included, so

          shows \<open>\<exists> k. u k = \<emptyset>\<close>
          \<comment>
          \<open>
            This lemma could easily be generalized ...
          \<close>

      is ONE formal comment.  `_MARKER_OPEN_RE` matches marker-plus-cartouche
      as a single token within a line, so the scanner sees a bare `\<comment>`
      and then a separate LIVE cartouche, and charges all the prose to the
      statement above it (`decl_end_line` 67 where the declaration ends at 62).
      D5 in the Scala port's `dev/DIVERGENCES.md`.
      **MEASURED, and the measurement says do not do it.**
      `scripts/probe_comment_split_scale.py`, counting the scanner's own
      failure (a marker still live in `live_source()` whose cartouche opens
      below) rather than a text pattern that guesses at the same shape:

          AFP           9,910 theories   1 site
          HOL/FOL/ZF    1,604 theories   0 sites

      **One occurrence in 11,514 theories** — Substitutions_Lambda_Free:63..67,
      costing 4 prose lines wrongly live, 9 tokens in them that name a real
      declaration, and one entry's `decl_end_line`.  The fix is a change to
      the tokenizer state machine, the highest-risk code in the package, to
      carry a pending marker across a line boundary.  That trade is not worth
      taking for one record: leave it unless a cheap route appears that does
      not touch `_scan_nonisar_spans`' state.  Kept on the list as a *measured*
      decision rather than deleted, so it is not re-litigated from the shape.

- [ ] `[decl-body-blank]` The residual 5 of `[decl-body-comment]`: a BLANK
      line before the note breaks the body scan before the note is reached.

          definition                                   HOL/UNITY/WFair.thy:35
                                        <- blank; the scan ends here
            \<comment> \<open>This definition specifies conditional fairness. ...\<close>
            transient :: "'a set => 'a program set" where

      so `transient` is still `src 35..43, body 35..35`.
      **Cost: 5 records** — 4 HOL (`WFair:35`, `Inc:14`, `DBuffer:11`,
      `Complex_Types:111`), 1 ZF (`GenPrefix:25`), 0 AFP.  Down from 50;
      the other 45 shipped as `[decl-body-comment]`.
      **The obvious fix was implemented, measured and REJECTED** — do not
      re-derive it.  "A blank cannot end what has not started" (skip the
      blank-line break while `body` is still empty) repairs all five and reads
      principled.  It also takes corpus-wide containment violations
      (`body_end > thy_end`, a body overlapping the NEXT declaration) from
      **82 to 719**, and the whole-AFP diff from 706 records to 1,799.  Any
      future attempt must report that containment number, not just the diff
      count: `scripts/probe_span_diff.py` prints both.
      Pinned as `expectedFailure` in
      `tests/test_decl_body_comment.py::TheBlankLineVariantIsStillOpen`, so a
      real fix reports an unexpected success rather than going unnoticed.
      Low priority at 5 records: filed so the rejection is not re-litigated.

- [ ] `[feature-audit]` Standing critical pass over each subcommand:
      output formats, defaults, and past design choices.  Re-benchmark
      against AWS AutoCorrode's `iq` tool
      (`https://github.com/awslabs/AutoCorrode/blob/main/iq/README.md`)
      to see which of its affordances we still lack.
      Open design questions (the headline comment-search gap, the
      `-n`/`--names` overload, and the `grep` owner-column span are now
      *closed* — see Done):
      - Optional: a comments-/prose-**only** view.  `grep --with-comments`
        is additive (live source *plus* comments); there's no way to see
        *only* the cartouche prose, which is what a PDF-commentary reader
        wants.

- [ ] `[keyword-scope]` The custom-command table is unioned over the whole
      ROOT, which is right for a session and too coarse for a corpus.  Both
      implementations mirror Isabelle's session-wide `Keywords.++`, but with
      the AFP `thys` directory as one root that puts Optics' `alphabet` in
      scope for Formula_Derivatives, whose `sublocale DA < DAs` /
      `alphabet init delta ...` continuation line then reads as a
      declaration.  16 records over 4 entries (Formula_Derivatives,
      MSO_Regex_Equivalence, UTP, Circus), and only when the whole AFP is
      passed as ONE root — each of the four is clean read as its own root.
      Fixing it means scoping the table per session, which changes the parse
      of every custom-command entry, so it belongs with the session model.
      Newly visible rather than newly introduced: before `[keyword-kind-quoted]`
      the quoted-kind bug kept `alphabet` out of the table and hid it.
      A second instance found while measuring [marker-decl]:
      `Isabelle_C/C_Appendices:831` mints a phantom `DEF` whose name is read
      out of a `text` block's prose, because Isabelle_C's `C_export_file` is in
      scope for a theory that never imports it.  Same shape, different session,
      and it shows the cost is not confined to one continuation-line accident.
      D4 in the Scala port's `dev/DIVERGENCES.md`.
      Sibling observation, same shape, deliberately not filed separately
      (D11): the method/attribute table is resolved from whichever declared
      sessions happen to have a BUILT HEAP, so `callers` can answer
      differently on two machines reading identical sources — heap union, the
      committed census union, or the Pure floor, three tables and three
      answers.  It is documented behaviour rather than a defect (CLAUDE.md
      says so), and it does not reproduce here — this machine has no AFP heaps,
      so the default and `ISABELLE_QUERY_NAMESPACE=committed` both answer 1261
      for `callers mono -c`.  Worth knowing before any measurement is quoted
      across machines.

- [ ] `[axiom-untyped]` An `axiomatization` constant with NO type ascription is
      not indexed.

          axiomatization glob_one and glob_inv     -- FOL/ex/.../Locale_Test1:722
            where glob_lone: \<open>prod(glob_one, x) = x\<close>

      indexes `glob_lone` (the axiom) but neither constant.  `_AXIOM_NAME_RE`
      is `([A-Za-z_][A-Za-z0-9_']*)\s*:` — it requires a colon, which is why a
      TYPED constant matches (`f :` out of `f :: "nat"`) and an untyped one
      never does.  The split is the type annotation, not the `and`.
      **Cost: 1 command, corpus-wide.**  Measured over the AFP, FOL, ZF and
      HOL/: exactly the one case above, and zero elsewhere.  That is the whole
      argument for leaving it: the colon is what stops the scan matching
      `where`, `and`, and any word in a proposition, and relaxing it to catch
      one declaration risks the over-match it was written to prevent.
      What would make it worth doing is a narrower rule rather than a looser
      one — before `where`, on the command's own lines, a bare `NAME (and
      NAME)*` list IS a constant list — which is a small grammar of its own,
      not a regex tweak.  Split out of `[axiom-names]`, whose other half
      shipped; the two turned out not to share a scan after all (the phantom
      was an unconditional placeholder, not a missing lookahead).

- [ ] `[grep-plain]` Optional `--plain`/`--raw` override on `grep`:
      force plain line-grep (no entry/comment parsing) instead of the
      `infer` parse policy.  Post-routing-refactor the parse mode is an
      explicit per-command property (`_section_from`'s `parse` arg):
      `largest`/`sorry` are `"syntax"`, `grep` is `"infer"` (decide per
      source from the `.thy` suffix, stdin defaulting to syntax-aware).
      This flag would let `grep` take a third value, `"plain"`, forcing
      plain line-grep — useful to override the suffix-less stdin guess
      (`git show REF:notes.md | query grep PAT - --plain`) or the rare
      on-disk case (a `.thy` grepped as raw text, or a theory under another
      extension).  Default stays `"infer"`.  Add the flag through one shared
      helper per the CLI contract.  Scope: `grep` only — `lines` is already
      ignore-syntax (a parse flag is inert) and `largest`/`sorry` *are* the
      entry view (plain guts them), so this is **not** a uniform
      all-commands flag.  Low urgency: `"infer"` parsing of non-theory
      content already degrades gracefully (every line reads as live, so all
      matches still show; only the owner column goes `—`).

- [ ] `[countstr]` **(exploratory — shape not settled).**  Record the itch,
      not a design.  The need: before a multi-site rewrite (a `replace_all`,
      a `sed`-style sweep), verify *exactly* how many times an exact,
      usually **multi-line** literal block occurs in a file, so the edit's
      reach is known up front — the "inventory the whole match set before
      claiming 'all instances'" discipline applied to a literal block.
      Today this needs an ad-hoc `python3 -c` count (or a throwaway script),
      which is precisely the gate-tripping shell the tool exists to retire.
      Why the shape feels off — the open tensions, all unresolved:
        - **Scope creep.**  `query` is theory-aware (entries, call graphs,
          syntax slices); a raw literal counter is generic text counting,
          nearer `grep -Fc` than anything semantic.  Does it belong here at
          all, or is reaching for `query` over `grep` here a category error?
        - **Not line-count.**  `grep -c` (and the planned `[grep-plain]`)
          count matching *lines*; the whole point is a *multi-line* block as
          one unit, which line-grep structurally can't express.  So this is a
          genuinely new counting mode, not a flag on existing `-c`.
        - **Literal vs regex.**  The `replace_all` use is *fixed-string*
          (exact block, no metachar surprises) — so `-F`/`--fixed`, not the
          regex `grep` takes.  A multi-line *regex* count is a different,
          slipperier beast; conflating them is part of why the shape wobbles.
        - **Input ergonomics (the worst part).**  Supplying a multi-line
          literal on argv is miserable; via stdin (`query countstr FILE -` /
          `< block`) the `-`/stdin sentinel is already the *file* side
          (`[stdin-path]`), so block-on-stdin + file-on-disk collide.  This
          tension is the main reason it isn't ready.
      Tentative leaning (do NOT build yet): a `--fixed`/`-F` + `--count`
      multiline mode on `grep` rather than a new verb — but only once the
      block-input ergonomics are solved.  Low value / low urgency: an inline
      one-liner covers it today; this is about retiring that one-liner, not
      unblocking anything.

- [ ] `[doc-graph]` **(exploratory — scope-uncertain.)**  A reference
      graph + activity survey over a project's **prose documentation**
      (design memos, spec docs, decision records) — the complement of the
      theory-entry graph.  As an Isabelle/Isar project accretes design
      docs, you periodically need to know which docs are stale
      (last-touched, commit churn) and which are actually referenced — and
      critically, *from where*.  Load-bearing lesson: a doc's real
      coupling often lives **outside the
      prose** — a `ROOT` description, a `.thy` `\<comment>`, a sibling
      test-harness's relative link — so a markdown-only "who cites this?"
      scan undercounts; the citer scan must span the whole tracked tree.
      Concrete prototype: a `doc-audit.py` — two modes, a per-file
      table (LASTCOMMIT / commit-count / lines / REF-A [cites from the
      active steering docs] / REF-ALL [cites anywhere in the tree]) and a
      `--refs FILE` location dump (`path:line`).
      Scope tension (same flavour as `[countstr]`): `query` is
      theory-aware (entries, call graphs, syntax slices over `.thy` under
      the `.isabelle-query` root); a doc-reference graph is generic prose
      over arbitrary files, nearer `grep -rl` + `git log` than anything
      semantic.  Does it belong in `query` at all, or is the doc corpus a
      sibling tool's job?  Two sub-questions if it lands here: (a) the
      citer scan wants the *whole* repo, which breaks the `t/`-only
      `.isabelle-query` scoping; (b) it shares machinery with the shipped
      `graph` verb (serialise an adjacency) and `refs` (citation rollup)
      but over a different node set (files, not entries).  Record the
      need; don't build until the scope call is made.

## Done

Nothing — by design. Completed work is recorded in its commit messages, which
carry the reasoning, the rejected alternatives and the before/after, and cannot
drift from the code the way a summary of them can. Recover one by its tag:

    git log --grep='\[locus-roundtrip\]'

See `CONTRIBUTING.md`.
