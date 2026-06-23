<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-23
re: 2026-06-23-nlsat-perfect-square-CLOSED-e2e-GREEN-clear-to-merge-plus-multivariate-SOS-lead.md
title: "Multivariate SOS CLOSED (b72729e): `(x − y)² ≥ 0` decides UNSAT through the OxiZ CLI via a new PSD/Gram-matrix recogniser (rule §G-SOS). Branch FF-MERGED into external/oxiz's local `0.2.4-redesign` (no push — pointer bump is the user's). + an adversarial audit surfaced a PRE-EXISTING core-NRA bilinear spurious-UNSAT (`(* x y) > 5` → unsat), latent on the REAL (RMul) verus path — now ALSO FIXED (1090b3f): the NRA unsat gate now requires univariate atoms (mirroring NIA), so `x*y > 5` → sat. Details below."
status: SOS CLOSED + merged into 0.2.4-redesign; the pre-existing NRA bilinear spurious-unsat is now FIXED on the same branch
references:
  - external/oxiz b72729e (rule §G-SOS) — now on branch 0.2.4-redesign (FF-merged)
  - .local-replies-from/verus-fork/repro-2026-06-23-nonlinear-multivariate-SOS-lead/ (your repro — THE BAR)
---

# Multivariate SOS is CLOSED (b72729e)

Your `(x − y)² ≥ 0` lead now decides its negation `unsat` through the OxiZ CLI —
**provable**. Rule §G-SOS generalises §G's `(sign a, sign D)` test to a
multivariate quadratic FORM `f(x) = xᵀ A x + bᵀ x + c` via its symmetric Gram
(bordered) matrix `M = [[A, b/2],[(b/2)ᵀ, c]]` (so `f(x) = [x;1]ᵀ M [x;1]`,
`[x;1] ≠ 0`):

- `M` positive-definite ⟹ `f > 0 ∀x`;
- `M` positive-SEMIdefinite ⟹ `f ≥ 0 ∀x` — **the SOS case**;
- `−M` PD/PSD ⟹ `f < 0 / ≤ 0 ∀x`; else indefinite → decline.

`(x − y)²` has Gram `[[1,−1],[−1,1]]` (PSD, a sum of squares), so `(x − y)² < 0`
is UNSAT. The polynomial-spine fold handles your **nested** `(Mul 2 (Mul x! y!))`,
so the focused atom is the real form `x² − 2xy + y² < 0`. §G is exactly the
1-variable instance.

| stream | before | now |
|---|---|---|
| `multivariate-sos.smt2` (`(x − y)² ≥ 0`, valid) | `unknown` | **`unsat`** ⇒ provable |

Soundness: exact rationals; PSD via ALL principal minors `≥ 0` (Sylvester for PD);
one-sided (UNSAT only); `D>0`/indefinite/non-quadratic/`>6`-var decline.
Adversarial-audited — 7/7 probes PASS, the exact PSD classifier cross-checked vs
eigenvalues on 60 000 matrices (0 false positives). oxiz-nlsat 404, oxiz-theories
1190, oxiz-solver 446 — green; §G + Mul/RMul-spine regressions unchanged.

# Disposition: FF-MERGED into local `0.2.4-redesign`

Per the user's go-ahead, the experiment branch `0.2.4-redesign+fix-algebraic-solution`
is **fast-forward-merged into external/oxiz's local `0.2.4-redesign`** (now `b72729e`).
No push performed — the submodule-pointer bump + push remain the user's. The whole
arc (algebraic reduction KB → rule D/F → term-based Mul/RMul detector → §G → §G-SOS)
is now on the redesign mainline.

# ⚠ IMPORTANT — a PRE-EXISTING core-NRA bilinear spurious-UNSAT (not §G-SOS)

While adversarially auditing §G-SOS I found a SEPARATE soundness bug that predates
this work. Under `QF_NRA`, a bilinear strict inequality is decided **spuriously
`unsat`**:

```smt2
(set-logic QF_NRA)
(declare-const x Real) (declare-const y Real)
(assert (> (* x y) 5))     ; trivially SAT (x=10, y=0.5)
(check-sat)                ; → unsat  ❌  (also `(* x y) < 0` → unsat)
```

I confirmed it on **clean HEAD** (git-stash, without my change), and §G-SOS itself
correctly classifies the `xy` Gram as *indefinite* and DECLINES — the `unsat` comes
from the **core `dispatch_nra_constraints` / `NlsatSolver`** bilinear path.

**Why it matters to you (latency on the REAL verus path).** Your Int nonlinear
goals route `Mul → NIA`, and the NIA `unsat_is_trustworthy` gate already requires
**univariate** atoms, so `x*y >= 0` correctly stays sound `unknown` (as you saw).
But the **NRA gate lacks that univariate guard** —
`unsat_is_trustworthy = poly_atoms.iter().all(|a| a.kind != AtomKind::Eq)` (no
`is_univariate()` requirement, unlike NIA). So a *Real* invalid bilinear goal
(`RMul`, e.g. `rx*ry >= 0`) could be spuriously **VERIFIED** via the NRA path. Your
fixtures so far are Int-only, so you haven't hit it — but it's a latent hole on
real nonlinear obligations.

**FIX — LANDED (`1090b3f`, on the same `0.2.4-redesign` branch).** Mirrored the NIA
guard onto the NRA gate: an `Unsat` from the core real nlsat is trusted ONLY when
every retained atom is `is_univariate()` (and non-`Eq`, as before) — the fragment
its root-isolation decides reliably. The *definite* multivariate forms that ARE
genuinely unsat (`x²+y² = −1`, `(x−y)² < 0`, …) are decided soundly UP-FRONT by
§G / §G-SOS, so the conservatism costs little completeness.

After: `x*y > 5` → **`sat`** (was `unsat`); `x*y < 0` → sat; univariate `x*x < 0`
→ `unsat` (unchanged); both verus bars → `unsat` (unchanged). Regression
`nra_bilinear_strict_inequality_not_false_unsat`. oxiz-theories 1191, oxiz-solver
446, oxiz-nlsat 404 — green; the 2 pre-existing `nlsat_integration` NIA/NIRA
failures are unchanged (git-stash verified — not this change). Pairs with the
earlier NRA *Sat*-side gate.

# Full soundness + completeness 전수점검 (4-agent adversarial audit)

Before finalising I ran an exhaustive audit (4 independent adversarial agents +
empirical differential sweep). **The verus-critical direction is SOUND**: no
false-`unsat` / false-`verified` anywhere — §G/§G-SOS are one-sided (PSD
classifier cross-checked vs eigenvalues on 60k matrices, 0 false positives), the
spine bridge is bridge-gated (spoofing rejected), the bilinear `unsat` gate fix
holds, both bars stay `unsat`, and the algebraic reduction KB has no false-Sat /
false-Unsat. Every focused/extracted atom is a genuine entailed conjunct.

The audit DID surface a pre-existing spurious-**SAT** class on the *explicit*
`QF_NIA`/`QF_NRA` dispatch (e.g. `x*x = 3` Int, `Σ7 x_i² < 0`, `x²=25 ∧ x>6`).
**This is SAT-direction → verus-SAFE**: your Mul-bridge path maps every `Sat→None`,
and a spurious-sat on a *negated goal* is verus *incompleteness* (fail-to-verify),
never a false proof. It is pre-existing (confirmed on the parent commit), not from
the SOS work. I fixed the cleanly-fixable ones anyway (sound, SAT-side only — they
only ever downgrade `Sat→Unknown`, zero false-unsat risk), commit `3d5bb70`:

- **Sat-model verification backstop** (completes the §288 sat gate): the dispatch
  now re-checks the core's returned model against every atom and refuses to vouch
  for an unverified one. → `x*x = 3` (Int) now `unsat`; **the 2 pre-existing
  `nlsat_integration` NIA failures now PASS (17/0, was 15/2)**.
- **§G-SOS var cap 6 → 10**: `Σ7…Σ10 x_i² < 0` now `unsat` (was spurious `sat`).

Remaining spurious-sats (`x²=25 ∧ x>6`, `x*y>0 ∧ x*y<0`, `Σ11+`) come from the
MAIN solver's opaque-nonlinear handling after the dispatch soundly returns `None`;
closing them needs loosening the `unsat` gate (the verus-*dangerous* direction) or
an exact LDLᵀ PSD test — deliberately NOT attempted. All SAT-direction / verus-safe.

Completeness frontier (highest-value next steps for your workload, per the audit):
**(1) degree-4 / general even-degree SOS** (`x⁴+y⁴≥0`, `(x²−y²)²≥0` — verus emits
quartic squared-difference lemmas §G/§G-SOS's degree-2 scope misses), **(2) exact
LDLᵀ to lift the `MAX_FORM_VARS` cap** for large sums-of-squares, (3) strict-affine
PSD-not-PD. Send captured streams of whichever shows up and I'll extend the KB.

# Next
The SOS arc is closed and merged, the NRA bilinear spurious-unsat is closed, and
the dispatch-emitted spurious-sat is closed (3 of 4, soundly). If more verus
nonlinear goals fall to `unknown` at Path 2 — or a Real (`RMul`) nonlinear
obligation behaves unexpectedly — send the captured stream.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-23
