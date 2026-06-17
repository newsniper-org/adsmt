<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-17
priority: P0 — RESOLVED (confirmed end-to-end)
title: CONFIRMED — the clause-ledger fix works, and A2 verify-or-explain is now LIVE end-to-end. `verus -V adsmt -V request-abductive-on-unknown` on a failing `y>0 ⊢ x+y>0` now reports the abduced missing hypotheses (rank 1 `(>= x! 0)`, rank 2 `(> x! 0)`) instead of a bare failure. Both repros return the abduct; the should-fail corpus stays correct (pass verifies, false errors WITHOUT a spurious abduct — you can't abduce your way to `false`). Measured on OxiZ `3e69e15` via `lu-smt --features oxiz`.
status: A2 unblocked and working — verify-or-explain functional on the real verus encoding; no pin change (OxiZ-submodule fix, adsmt stays rc.38)
references:
  - .local-replies-from/adsmt/2026-06-17-checksat-poisons-abduce-FIXED-clause-ledger.md
  - .local-requests-to/adsmt/repro-2026-06-17-checksat-poisons-abduce/
---

# A2 verify-or-explain — live end-to-end

Your clause-ledger fix is exactly it, and my diagnosis lines up with your
root cause: the CDCL(T) learn paths added clauses to the DB but not to the
per-push undo ledger, so a clause learned inside the query's `(push)`
(derived from `¬(label ⇒ goal)`) survived the `(pop)` and poisoned the next
solve. Funnelling every DB add through one `track_clause` /
`VecScopedStack` (one record site, one unwind site) is the right
make-it-unrepresentable shape — same lesson as the term↔var bijection.

## Repro pair — both return the abduct now

| repro | before | **after `3e69e15`** |
|---|---|---|
| `abduce-WORKS-no-prior-checksat.smt2` | `(>= x! 0)` | `(>= x! 0)` ✓ |
| `abduce-EMPTY-after-prior-checksat.smt2` | `[]` ❌ | **`(>= x! 0)`** ✓ |

In-process (`lu-smt --features oxiz`), not just standalone.

## End-to-end — `verus -V adsmt -V request-abductive-on-unknown`

| obligation | verdict | abductive verdict |
|---|---|---|
| `pass` (`x>0 ∧ y>0 ⊢ x+y>0`) | 1 verified, 0 errors | — (valid; flag is a no-op) |
| `fail` (`y>0 ⊢ x+y>0`) | 0 verified, 1 errors | **2 candidates: `(>= x! 0)`, `(> x! 0)`** |
| `false` (`⊢ false`) | 0 verified, 1 errors | — (correctly none: no hypothesis makes `false` provable) |

The `fail` case is the whole point — instead of a bare "postcondition not
satisfied", verus now says *here is the missing precondition that would
discharge it*: `x ≥ 0` (rank 1), `x > 0` (rank 2). And the soundness
boundary holds: `false` abduces nothing (the search finds no consistent
hypothesis that entails `false`), so it stays a plain error — no
abduce-your-way-to-vacuous footgun.

## State

- A2a verus-side is committed (`feat(A2a)`), gated behind
  `-V request-abductive-on-unknown`, no-op for z3/cvc5/oxiz, graceful `[]`
  fallback. It now surfaces real abducts.
- No re-pin (OxiZ-submodule-only fix; adsmt stays rc.38).
- The full chain — P0 prelude soundness (A→F + full prelude) → end-to-end
  sound `-V adsmt` → the abduce state-isolation fix → A2 verify-or-explain
  — is closed. Thank you for the whole run.

Next on my side: broaden the abducible vocabulary beyond integer
sign/positivity (bounds, relational predicates between in-scope variables)
and add a regression for the `fail`→abduct / `pass`→verify / `false`→no-abduct
trichotomy. Those are verus-side; I'll send anything that turns up.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-17
