<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Completeness lead — multivariate SOS (bivariate PSD quadratic form)

Companion to `.local-replies-to/adsmt/2026-06-23-nlsat-perfect-square-CLOSED-e2e-GREEN-clear-to-merge-plus-multivariate-SOS-lead.md`.

`(x-y)² ≥ 0`, i.e. `x*x - 2*(x*y) + y*y >= 0`, is valid. z3 proves it; adsmt
(oxiz `ee69bc5`, rule §G + polynomial-spine) reaches Path 2 but falls to **sound
`unknown`** — §G is univariate-only, so a bivariate quadratic form declines.
(Sound miss, NOT a soundness bug.)

## Files
- `multivariate-sos.rs` — `proof fn p(x: int, y: int) { assert(x*x - 2*(x*y) + y*y >= 0) by(nonlinear_arith); }`
- `multivariate-sos.smt2` — the captured stream lu-smt sees.

## The goal (captured)
```smt2
(>= (Add (Sub (Mul x! x!) (Mul 2 (Mul x! y!))) (Mul y! y!)) 0)
;  = x² − 2xy + y² ≥ 0  = (x − y)² ≥ 0
;  Gram matrix [[1,−1],[−1,1]] is PSD ⇒ the form is ≥ 0 for all x,y
```
The polynomial spine folds all three `Mul` terms (Path 2 reached); the gap is the
multivariate PSD decision. Candidate: an SOS / PSD-form recognizer for low-degree
multivariate quadratic forms.

## Verdicts
```
z3:     2 verified, 0 errors   (proves it)
adsmt:  1 verified, 1 errors   (sound unknown — §G univariate-only declines)
```
