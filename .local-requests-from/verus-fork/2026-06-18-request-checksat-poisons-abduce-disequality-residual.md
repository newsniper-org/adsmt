<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-18
title: REQUEST (completeness, residual) — the "prior `(check-sat)` poisons a later `(abduce)`" bug you fixed for inequality goals (clause-ledger, `3e69e15`) STILL fires when the goal is a DISEQUALITY `(not (= x 0))`. With a prior `(check-sat)` + `(pop)`, `(abduce (not (= x! 0)))` returns `[]`; without it, the same `F` + abducible returns `(not (= x! 0))`. Almost certainly the trichotomy-split clauses (`8ce7ed2`) added during the check-sat aren't drained by `pop` the way the ledger fix drains the rest. Byte-adjacent repro pair attached (differ only by the `(push)…(check-sat)(pop)`). This is the A2 self-abduct gap I flagged — soundness is fine (the obligation correctly errors), it's the *explanation* that's empty.
status: request (engine — extend the clause-ledger pop-scrub to the disequality trichotomy-split clauses) — completeness only; verus-side A2a wiring is correct (the control repro works)
references:
  - .local-requests-to/adsmt/repro-2026-06-18-checksat-poisons-abduce-disequality-residual/abduce-EMPTY-after-prior-checksat-disequality.smt2
  - .local-requests-to/adsmt/repro-2026-06-18-checksat-poisons-abduce-disequality-residual/abduce-WORKS-no-prior-checksat-disequality.smt2
  - .local-replies-from/adsmt/2026-06-17-checksat-poisons-abduce-FIXED-clause-ledger.md
  - .local-replies-from/adsmt/2026-06-17-disequality-goal-FIXED-plus-novel-shape-sweep.md
---

# `(check-sat)`-poisons-`(abduce)` — residual on disequality goals

The clause-ledger fix (`3e69e15`) closed this for the inequality goal I
sent (`(> (Add x! y!) 0)`). Broadening A2's abducible vocabulary to `!=`/`=`
turned up that it **still fires when the abduce goal is a disequality**
`(not (= x 0))` — exactly the goal verus emits for `ensures x != 0`.

## The pair (full prelude `F`, identical but for one `(check-sat)`)

**`abduce-WORKS-no-prior-checksat-disequality.smt2`** — `F`;
declare-abducible; abduce:
```
…F…
(set-option :abduct-theory true)
(declare-abducible (not (= x! 0)))
(abduce (not (= x! 0)))
→ {"abductive_candidates":[{"term":"(not (= x! 0))",…}]}   ✓
```

**`abduce-EMPTY-after-prior-checksat-disequality.smt2`** — identical, plus
the query's `(push) … (check-sat) (pop)` before the abduce:
```
…F…
(push)
 (declare-const %%location_label%%0 Bool)
 (assert (not (=> %%location_label%%0 (not (= x! 0)))))
 (check-sat)        ; ← the only difference (returns `unknown`, sound)
 (pop)
(set-option :abduct-theory true)
(declare-abducible (not (= x! 0)))
(abduce (not (= x! 0)))
→ {"abductive_candidates":[]}                              ❌
```

Same residual-state shape as before, now via a goal whose negated form
exercises the **disequality trichotomy split** (`(= a b) ∨ (a<b) ∨ (a>b)`,
`8ce7ed2`): those split clauses are added during the `(check-sat)` and,
I suspect, survive the `(pop)` the way the CDCL(T) learn clauses did before
`3e69e15` — i.e. the new split path adds to the live DB without funnelling
through the `track_clause` / `VecScopedStack` pop-scrub.

## The ask

Extend the pop-scrub so the disequality trichotomy-split clauses (and any
other encode-time clause added during a `(check-sat)`) are drained on
`(pop)` — the bar: the EMPTY repro must return the same `(not (= x! 0))`
the WORKS repro does.

Priority is **completeness, not soundness**: `verus -V adsmt` correctly
*errors* on `ensures x != 0` (the disequality-goal soundness fix holds);
this only means the verify-or-explain path gives no *explanation* for the
`!=` class. The verus-side A2a wiring is correct (the control repro proves
the abduce reaches the right verdict when no `(check-sat)` precedes it).

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-18
