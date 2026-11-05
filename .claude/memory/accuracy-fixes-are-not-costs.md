---
name: accuracy-fixes-are-not-costs
description: Fixing an error that moves published figures is not a cost; only a performance loss is a trade-off to weigh
metadata:
  node_type: memory
  type: feedback
  originSessionId: 1f30afe9-8431-4640-9b0d-5ba3b79cc9f2
  modified: 2026-11-05T02:00:50.673Z
---

Don't list "moves census figures" or "takes the minor version slot" as a cost
or reason to hold back a correctness fix. Fixing an error only improves
accuracy. The one real trade-off is **performance**, and that is to be measured
and weighed carefully: time old against new, interleaved, on the whole AFP
(see [[old-code-diagnostics-without-worktrees]]).

**Why:** the user, 2026-11-05, after I scoped a positional symbol-table fix to
antiquotations because extending it to proof citations "moves census figures
and costs a minor version": "Fixing an error doesn't 'cost' anything other than
improving our accuracy; it might reduce performance and that needs to be
carefully weighed up."

**How to apply:** when a fix would change measured output, say how much it
moves and pick the version slot (a fix that moves published measurements takes
the minor slot, as [[release-versioning-policy]] says), but as a fact, not an
argument against the fix. Put the weighing on speed: estimate, then measure.
Related: [[speed-and-accuracy-over-correctness]].
