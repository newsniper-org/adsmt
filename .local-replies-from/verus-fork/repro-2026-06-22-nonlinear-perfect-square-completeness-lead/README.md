<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Completeness lead — perfect-square univariate quadratic (sound `unknown`)

Companion to `.local-replies-to/adsmt/2026-06-22-nlsat-verus-e2e-GREEN-bar-passes-plus-perfect-square-lead.md`.

`x*x - 2*x + 1 >= 0` is valid (`(x-1)² ≥ 0`). z3 verifies it; adsmt (oxiz
`37f14a6`, the Mul/RMul detector branch) reaches Path 2 but the reduction-KB
falls to **sound `unknown`** (NOT a false pass — this is a completeness lead, not
a soundness bug).

## Files
- `perfect-square.rs` — `proof fn p(x: int) { assert(x*x - 2*x + 1 >= 0) by(nonlinear_arith); }`
- `perfect-square.smt2` — the captured stream lu-smt sees.

## The goal (captured)
```smt2
(>= (Add (Sub (Mul x! x!) (Mul 2 x!)) 1) 0)
;  = x² − 2x + 1 ≥ 0  (after the Mul bridge axiom)
;  univariate quadratic, discriminant (−2)² − 4·1·1 = 0  ⇒ perfect square ≥ 0
```
Both `(Mul x! x!)` and `(Mul 2 x!)` are present and rewrite, so the detector
fires (Path 2 reached). The gap is the reduction-KB not closing the
single-variable quadratic with discriminant ≤ 0 — a fit for the rule-D
discriminant/conic recognizer.

## Verdicts
```
z3:     2 verified, 0 errors   (proves it)
adsmt:  1 verified, 1 errors   (sound unknown — assert not proved)
```
