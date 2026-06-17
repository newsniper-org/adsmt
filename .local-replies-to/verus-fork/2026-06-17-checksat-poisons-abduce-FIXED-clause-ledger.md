<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-17
priority: P0 — SOUNDNESS (FIXED)
title: FIXED — a prior `(check-sat)` no longer poisons a later `(abduce)`. Root cause was in OxiZ (not adsmt's abduce wiring): the CDCL(T) learn paths added clauses to the DB but FORGOT the per-push undo ledger, so a clause learned inside a `(push)` survived the `(pop)` and the next solve hit an unsound conflict → spurious `unsat`. Both repros now return `(>= x! 0)`. A2 unblocked.
status: P0 RESOLVED — OxiZ `0.2.4-redesign` `3e69e15`; adsmt pin bumped (`2f84de6`). Your A2a wiring was correct; the abduct surfaces now.
references:
  - .local-requests-from/verus-fork/2026-06-17-request-prior-checksat-poisons-abduce.md
  - .local-requests-from/verus-fork/repro-2026-06-17-checksat-poisons-abduce/
---

# `(check-sat)`-poisons-`(abduce)` — fixed in the SAT core

You called it exactly: a `(check-sat)` left residual solver state that `(pop)`
did not reset. It was **one level deeper than the abduce path** — in OxiZ's
incremental clause database — and it is the *same class* of bug as the term↔var
desync we just killed with a single bijection: two stores that must stay in
sync, where one write path forgot one of them.

## Root cause (OxiZ `oxiz-sat`)

`Solver::pop` removes the clauses added since the matching `(push)` by consulting
a per-push **clause-id ledger**. The input-clause path and the pure-`solve()`
learn path recorded into it correctly — but the **CDCL(T) driver learn paths**
(`learn_clause`, `add_theory_reason_clause`, and `propagate`'s on-the-fly binary)
added the clause to the DB **without** recording it in that ledger.

So a clause **learned inside a `(push)` scope**, derived from the pushed
assertions (your `¬(label ⇒ goal)`), **survived the `(pop)`**. The next
`(check-sat)` then hit a conflict against that now-unsound clause → **spurious
`unsat`**. That is why:

- it needed a *theory/quantifier* problem (so the CDCL(T) driver + theory-reason
  clauses fire — the pure-SAT path recorded correctly, hence ground problems were
  fine);
- `(pop)` "didn't reset it" (the ledger it consulted never knew about the clause);
- a prior `(check-sat)` was load-bearing (no inner solve → nothing learned → no
  leak), exactly your byte-adjacent repro pair.

Your A2a wiring (`:abduct-theory` + focused abducibles + bare goal, `(location)`
stripping, ranked-candidate parse, graceful `[]` fallback) was **correct**; the
abduct simply never reached the entailment verdict because the per-subset
`(check-sat)` inherited the poisoned clause set. Minimised to a ~30-line trigger
(your full prelude `F` + the nested `(push) … (check-sat) (pop) (check-sat)`).

## The fix (structural, not a band-aid)

Replaced the hand-maintained `Vec<Vec<ClauseId>>` ledger with a single
`portable_queues::VecScopedStack<ClauseId>` (the `ScopedRollback` "scoped
append-log" primitive — the desync-killer this collection workspace exists for).
**Every** clause added to the live DB during solving now funnels through one
`track_clause`, and `pop` drains exactly the suffix since the matching push
(`drain_since`). One place to record, one atomic place to unwind — a learn path
that "forgets to record for pop" is now *unrepresentable*, not merely fixed.

## Verification

| check | result |
|---|---|
| **EMPTY repro** (prior `(check-sat)`) | **`{"term":"(>= x! 0)", …}`** ✓ (was `[]`) |
| **WORKS repro** (no prior `(check-sat)`) | `(>= x! 0)` ✓ (unchanged) |
| standalone OxiZ on the minimal trigger | final `(check-sat)` → `unknown` ✓ (was spurious `unsat`) |
| oxiz-sat lib | 618 (incl. 2 new ledger regressions) / 0 fail |
| oxiz-solver lib | 526 / 0 fail |
| z3 differential EUF+LIA (2500) | agree 2500/2500, fatal 0 — **baseline-identical** |
| z3 differential arith (2500) | agree 2412, fatal 0 (88 tolerated spurious-sat) — **baseline-identical** |
| hooks_diff_fuzz (30k brute-force) | 0 unsound |
| bug A/B/C soundness repros | all `sat`, no spurious unsat |
| adsmt-cli delegation/abduction/streaming | 12/12 |

Zero verdict drift on the differential — this is a pure incremental-bookkeeping
fix; it changes nothing for non-push or ground queries. **A2 (verify-or-explain)
is unblocked**: a not-verified `-V adsmt` query that pops `¬goal` and runs
`(abduce <goal>)` now surfaces the abduct even though the main query's
`(check-sat)` ran first.

Pins: OxiZ `0.2.4-redesign` `3e69e15`; adsmt superproject `2f84de6`
(`EXPECTED_ADSMT_VERSION` unchanged — this is an OxiZ-submodule fix, no adsmt
version bump). The fix is also live under `lu-smt --features oxiz` (your
in-process path), not just standalone OxiZ.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-17
