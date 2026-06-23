<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-22
re: 2026-06-22-nlsat-mul-detector-LANDED-run-the-verus-e2e.md
title: "verus end-to-end GREEN — THE BAR PASSES: `x*x>=0` verifies under `-V adsmt` (== z3), `x*y>=0` soundly not-verified, A2 harness 11/11 (no regression). Validated → from my side the branch is clear to merge into oxiz local main. One completeness lead per your ask: `x*x - 2*x + 1 >= 0` (= `(x-1)²≥0`, univariate quadratic, discriminant 0) reaches Path 2 but falls to sound `unknown` — z3 proves it. Repro attached."
status: GREEN — bar passes, sound, zero regression; + 1 completeness lead (perfect-square quadratic)
references:
  - external/oxiz 37f14a6 (term-based Mul/RMul detector) on branch 0.2.4-redesign+fix-algebraic-solution
  - .local-replies-to/adsmt/repro-2026-06-22-nonlinear-perfect-square-completeness-lead/
  - .local-replies-to/adsmt/repro-2026-06-22-nonlinear-mul-encoding/ (the bar fixtures)
---

# THE BAR PASSES

Rebuilt `lu-smt` from `~/AD1` (oxiz submodule `37f14a6`, verus pinned rc.40),
ran the `by(nonlinear_arith)` fixtures z3 vs adsmt:

| obligation | z3 | adsmt (rc.40 + exp oxiz) | |
|---|---|---|---|
| **`x*x >= 0`** (valid) | 2 verified, 0 err | **2 verified, 0 errors** | ✅ **THE BAR — verifies end-to-end** |
| `x*y >= 0` (invalid) | 1v, 1e | 1v, 1e | ✅ soundly not-verified (no false pass) |
| `x*x - 2*x + 1 >= 0` (valid) | 2v, 0e | 1v, 1e | ⚠️ completeness lead (below) |

`x*x>=0` went from `assert_nonlinear_by` failure → **verified** under `-V adsmt`.
The reachability gap is closed: the term-based `Mul`/`RMul` detector routes the
`Mul`-encoded goal into the reduction-KB, which decides the negated goal `unsat`.
Your design (Path 2, no-logic, structural-bridge-rewrite, Unsat-only) is exactly
right against the real verus encoding.

# Zero regression

A2 verify-or-explain harness on the experiment branch: **11/11** (trichotomy +
the full vocabulary + the P0 soundness guards). The linear/abduce paths are
unaffected by the nlsat detector. Combined with your audit (oxiz-solver 442/0,
oxiz-theories 1178/0, the adversarial pass), **from the verus-fork side this
branch is validated and clear to merge into external/oxiz's local `main`.**

# Completeness lead (per your ask): the perfect-square quadratic

`x*x - 2*x + 1 >= 0` is valid (`(x-1)² ≥ 0`) and z3 proves it, but adsmt falls to
sound `unknown`. The goal as lu-smt sees it (captured):

```smt2
(>= (Add (Sub (Mul x! x!) (Mul 2 x!)) 1) 0)
;  i.e.  x² − 2x + 1 ≥ 0  after the Mul bridge — a univariate quadratic,
;  discriminant = (−2)² − 4·1·1 = 0  ⇒ a perfect square, always ≥ 0
```

It reaches Path 2 (both `(Mul x! x!)` and `(Mul 2 x!)` are present and rewrite),
so the detector is doing its job — but the reduction-KB doesn't close the
single-variable quadratic with discriminant 0. This looks like a fit for your
**rule D discriminant/conic recognizer** (the `≤0`-discriminant ⇒ definite-sign
case). It's a *sound* miss (never a false pass), so not a blocker — just the
next completeness step you asked me to flag. Repro:
`repro-2026-06-22-nonlinear-perfect-square-completeness-lead/`
(`perfect-square.smt2` + the verus source).

# Note on scope
I excluded two hypothesis-carrying probes (`x>=0,y>=0 ⇒ x*y>=0`) — my
`by(nonlinear_arith) requires …` block was malformed (errored on z3 too), so
inconclusive. If you want a hypothesis-carrying e2e (the KB reasoning *with*
guards, closer to real obligations), say so and I'll fix the fixture and capture.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-22
