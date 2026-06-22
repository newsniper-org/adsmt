<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-21
priority: P2 — regression (abduce over an equality goal hangs on the prelude)
title: REGRESSION since `605f175` (rc.39.2, the native Bool-eq fix), still present on rc.39.3 — `(abduce)` on an equality goal `(= (Sub x! y!) 0)` over the full verus prelude HANGS (native churn, >300 s; was a clean PASS surfacing `(= x! y!)` on `c9ed6e1`). SCOPED to the abduce/explain path: the same obligation's main `(check-sat)` (no abduce) returns `unknown` in ~1 s, so core `verus -V adsmt` is unaffected. Removing the equality abducibles does NOT fix it — the equality GOAL + the new Bool-eq→iff CNF rewrite over the prelude is the trigger.
status: live request — A2 verify-or-explain harness regressed 11/11 → 10/11 (only the `abduct-eq-vars` row); core verification sound and unaffected
references:
  - 605f175 fix(engine): native Bool-predicate-trigger e-matching — the suspected cause (cnf.rs rewrite_bool_iff / quant.rs trigger-into-=)
  - .local-replies-to/adsmt/repro-2026-06-21-eqvars-abduce-hang/  (THE captured full-prelude .smt2 + the main-session-only control)
  - .local-replies-from/adsmt/2026-06-19-native-bool-predicate-trigger-ematching-FIXED-plus-rc392-cut.md
---

# What regressed

The A2 `abduct-eq-vars` fixture (`proof fn p(x: int, y: int) ensures x - y == 0`)
abducts `(= x! y!)` for the goal `(= (Sub x! y!) 0)`. Across releases on the
SAME fixture / verus / harness (only the `lu-smt` binary changes):

| lu-smt | `abduct-eq-vars` |
|---|---|
| `c9ed6e1` (rc.39.1+abduce-deferral) | **PASS** — surfaced `(= x! y!)`, finished < 300 s |
| `605f175` (rc.39.2, native Bool-eq fix) | **HANG** — > 300 s |
| `7fe44d5` (rc.39.3, CCFV) | **HANG** — > 300 s (CCFV is OxiZ-side; doesn't touch this) |

Measured on the captured query (the exact stream `lu-smt` sees), rebuilt
binaries from `~/AD1`:
- native-only build: HANG (70 s timeout, 100 % CPU — compute-bound churn, not I/O wait).
- oxiz build: HANG (70 s timeout).

# Scope — abduce-only; core verification is fine

Truncating the captured stream to just before the abductive block (the main
verification session + a terminal `(check-sat)`) finishes in **~1 s** →
`unknown`. So `verus -V adsmt` (plain verification) on equality postconditions is
**unaffected** — only `-V request-abductive-on-unknown` hangs, on the abduce
per-subset search over an equality goal. That's why this is P2, not P0.

# Isolation

- Removing the equality abducibles (`(= …)` / `(not (= …))`) from the captured
  query does **not** stop the hang — so it's not the equality *abducibles*; it's
  the equality **goal** `(= (Sub x! y!) 0)` (where `Sub` is the prelude's
  arithmetic function with its own `:pattern` axioms) under the abduce
  per-subset search.
- Does not reproduce on a small `F` (the prelude's `Sub` axioms are needed).
- Timing + the `605f175` boundary point at the native Bool-eq→iff CNF rewrite
  (`cnf.rs rewrite_bool_iff`) and/or the trigger-into-`=` change (`quant.rs`):
  over the full prelude, the equality-goal abduce now appears to generate a
  clause/instantiation blowup (or a matching loop) per per-subset `check-sat`,
  where before it terminated.

# The ask

Please look at why the equality-goal `(abduce)` over the prelude no longer
terminates under the `605f175` native Bool-eq handling. The bar: the
`abduct-eq-vars` repro surfaces `(= x! y!)` again (or at least terminates with a
verdict) within the harness budget. Repro attached (the full captured stream +
the main-session-only control that finishes in ~1 s). Likely the same
`rewrite_bool_iff` / `:rlimit` interaction needs a guard so the equality-goal
per-subset solve bails to `unknown` instead of churning.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-21
