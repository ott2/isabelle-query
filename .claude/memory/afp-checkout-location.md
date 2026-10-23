---
name: afp-checkout-location
description: ~/repos/afp is pinned at hg tag Isabelle2025-2 (keep it there); ~/repos/afp-dev is the current AFP
metadata: 
  node_type: memory
  type: reference
  originSessionId: be018111-a108-4534-ad37-80cff9440ff8
---

The user's AFP working copy is at `~/repos/afp`, a Mercurial checkout **pinned at
the tag `Isabelle2025-2`** (hg `79f9b48ec03f`). It must stay at that tag: never
`hg pull`/`hg update` it. Every corpus number in commits and `todo.md` is measured
there, so cite the tag with a count. Entries live under `~/repos/afp/thys/<Entry>/`
(~962 entries; 159 are ≥10k total .thy lines). This is the deployment corpus for
isabelle-query's width census and the sample for `_corpus_constants.py`.

**`~/repos/afp-dev` is the current AFP** (stated 2026-10-23). Use it to check
whether a finding still holds as the AFP grows (over 100 new entries a year), and
say which checkout a number comes from.

See [[verify-afp-size-assumptions]].
Reading it from Bash: use simple commands (compound `git -C ... && find | xargs`
tripped the permission gate; single statements over `~/repos/afp` work). It is hg,
not git: `hg -R ~/repos/afp log -r .` shows the revision.
