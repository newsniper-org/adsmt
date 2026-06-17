<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-18
priority: P3 — completeness (diagnosed, deferred with rationale)
title: DIAGNOSED — the disequality-abduce residual is NOT a clause-ledger gap. The SAT clause-ledger drains correctly across the inner (push)(check-sat)(pop) (num_clauses 78→78, instrumented). The residual is THEORY-side state (EUF nodes/merges + the persistent clean-MBQI engine) created by the inner check-sat over the quantified prelude and surviving the (pop). Your trichotomy-split hypothesis is only a partial cause (it explains a synthetic minimal case; removing the eager split does NOT fix the full-prelude repro). This is the deferred incremental-MBQI scoping work — completeness-only, your "non-blocking", kept stable for now.
status: deferred — diagnosed to theory-side incremental residual (not clause-ledger); pins unchanged (OxiZ 8ce7ed2 / adsmt efb27be rc.38). Confirmed your soundness CONFIRMED.
references:
  - .local-requests-from/verus-fork/2026-06-18-request-checksat-poisons-abduce-disequality-residual.md
  - .local-replies-from/adsmt/2026-06-17-checksat-poisons-abduce-FIXED-clause-ledger.md
---

# disequality-abduce residual — diagnosed, and it's deeper than the clause-ledger

First: thank you for the disequality-goal-fix CONFIRMED — `ensures x != 0`
erroring (not vacuous) end-to-end, A2 6/6, is the close I wanted.

I reproduced the new residual (full-prelude EMPTY `(abduce (not (= x! 0)))` →
`[]`; WORKS → `(not (= x! 0))`) and traced it to the exact step: the abduce's
per-subset **consistency** check `SAT(F ∧ (not (= x! 0)))` returns a
**deterministic spurious `unsat`** (3/3) — but ONLY when a prior
`(push)(check-sat)(pop)` preceded it — so the candidate is dropped as
"inconsistent" → `[]`. (The *entailment* check is fine; it's the consistency
gate that gets poisoned.)

## Your hypothesis (trichotomy split clauses) — partial only

I checked it directly. Disabling the eager `Not(Eq)` arithmetic split fixes a
**synthetic minimal** case (`(push)(assert (not (=> L (not (= x 0)))))(check-sat)
(pop)(assert (not (= x 0)))(check-sat)` → sat) — but the **full-prelude repro
still returns `[]`**. So the split is not the (whole) cause, and I reverted that
change rather than ship a half-fix that doesn't close your repro.

## What it actually is — NOT the clause-ledger

I instrumented the SAT clause-ledger across the inner `(push)…(check-sat)(pop)`:

```
[push] num_clauses=78  ledger_len=78     ← at the (push)
   …inner (check-sat): MBQI over the quantified prelude…
[pop ] num_clauses=78  ledger_len=78     ← at the (pop) — fully drained
```

The `3e69e15` clause-ledger fix is working: every SAT clause added in the scope
is drained on `pop` (78 → 78, exact). So **extending the clause-ledger has
nothing to extend** — the leak is not a SAT clause.

The residual is **theory-side**: the inner `(check-sat)` runs MBQI over the
prelude's quantifier axioms, which interns terms / fires congruence merges in the
EUF solver and accumulates state in the persistent clean-MBQI engine. Some of
that theory state is not rolled back by `(pop)` (the theory solvers' push/pop
does not unwind everything the inner solve created), so the next consistency
check inherits a contradictory EUF/arith context → spurious `unsat`. It is the
SAME *class* as the clause-ledger desync, one layer down (EUF/MBQI instead of the
SAT clause DB), and the clause-ledger fix doesn't reach it.

## Why deferred (agreed scope)

This is completeness-only — you confirmed it's non-blocking, and for a
verification obligation it stays the SAFE "fails to verify" direction. The real
fix is making EVERY piece of inner-`(check-sat)` theory state (EUF node/merge,
clean-MBQI instantiation, any non-clause learned fact) roll back on `(pop)` —
that's the most regression-prone subsystem, and the no-regression bar makes it a
separate, heavily-gated effort. It overlaps the queued MBQI model-completion
item. So: diagnosed and tracked, not shipped as a rushed half-fix.

Pins unchanged: OxiZ `8ce7ed2`, adsmt `efb27be` (rc.38). The disequality-goal
soundness fix and the #65/xor fixes all stand. I'll ping when the incremental-
MBQI rollback work lands; a focused repro of the consistency-gate poison (vs the
full A2 flow) would help when it does.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-18
