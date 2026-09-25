---
name: authorship-credit
description: How to credit authorship on the query / isabelle-query project artifacts
metadata: 
  node_type: memory
  type: feedback
  originSessionId: ef4b3238-179f-4694-a1b1-cea8fbcab1b1
  modified: 2026-09-22T14:26:09.210Z
---

When crediting authorship on artifacts for the `query` / isabelle-query project (pyproject `authors`, README, acknowledgments, etc.), credit **"András Salamon, with Claude Opus 4.6, 4.7, 4.8, and 5"** — not just the human, and not a single model version.

**Why:** the work was developed collaboratively with Claude across those Opus versions over time; the user explicitly asked for this phrasing. The list grows as later models contribute — Opus 5 was added on 2026-08-01, when it shipped the issue-#2 fix and v0.5.1.

**How to apply:** put the human author in structured `authors` fields, and name the Claude Opus 4.6 / 4.7 / 4.8 / 5 collaboration in README "Authors"/acknowledgment prose. This is distinct from the per-commit `Co-Authored-By:` trailer, which still goes on individual commits and names **the model doing the work** (currently `Claude Opus 5 (1M context) <noreply@anthropic.com>`); CLAUDE.md carries the verbatim trailer, so bump it there too when the working model changes. See [[user-andras-salamon]].

**The stored phrasing is a default, not the decision** — see [[claude-md-is-guideline-not-authority]]. The credit line tracks who actually did the work, so it grows for both new models *and* outside contributors. PR #11 (2026-09-22) is the first outside contribution: seven commits authored by David Wang, all trailered `Co-Authored-By: Claude Fable 5.1`, adding `instances` / `codeqs` / `sites.py`. Check the real authorship before reusing the line above. Applied 2026-09-25 as a separate contributor line ("`instances` and `codeqs` by David Wang, with Claude Fable 5.1.") in README and the pyproject comment. **The user decided David is a contributor only: no `authors` entry, no email in pyproject** — their commits use a GitHub noreply address, and the address is theirs to choose.

**A commit message is never an artifact for this purpose** — it takes the trailer alone, and that includes the version-bump commit whose message CI publishes verbatim as the GitHub Release body. v0.7.0's notes carried the credit line and were corrected at v0.8.0 (2026-09-01); every other release is trailer-only. "Artifacts" here means the published files — README, pyproject — not everything the project emits.
