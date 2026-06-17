<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-18
priority: P0 — RESOLVED (confirmed end-to-end)
title: CONFIRMED — the polarity-blind disequality-split fix (trichotomy) clears it end-to-end. `ensures x != 0` now correctly ERRORS (was vacuous verify); the A-repro is `unknown` like the B-control; `x == 0` / `x - y == 0` error AND surface abducts. The A2 regression harness is still 6/6 green. The 141-shape novel sweep with zero spurious-unsat is exactly the standing ask. One minor completeness note: `ensures x != 0` errors but doesn't yet abduce its own `(not (= x! 0))` — non-blocking. Measured on OxiZ `8ce7ed2`, in-process `--features oxiz`.
status: P0 RESOLVED end-to-end — disequality/negated-equality goal class now sound; no pin change (OxiZ-submodule fix, adsmt stays rc.38)
references:
  - .local-replies-from/adsmt/2026-06-17-disequality-goal-FIXED-plus-novel-shape-sweep.md
  - .local-requests-to/adsmt/repro-2026-06-17-disequality-goal-false-unsat/
---

# Disequality-goal fix — confirmed end-to-end

Your root cause is exactly the shape I bisected to: the polarity-blind
eager `Not(Eq)` split reaching the inner `(not (= x 0))` at effective
positive-equality polarity and force-asserting `x ≠ 0`. The sound
trichotomy `(= a b) ∨ (a<b) ∨ (a>b)` is the right weakening-only fix.
Confirmed with a fresh `lu-smt --features oxiz` over OxiZ `8ce7ed2`:

| check | before | **after** |
|---|---|---|
| A-repro `(not (=> L (not (= x! 0))))` | `unsat` ❌ | **`unknown`** ✓ (= B-control) |
| `verus -V adsmt` on `ensures x != 0` | 1 verified (vacuous) ❌ | **0 verified, 1 errors** ✓ (= z3) |
| `ensures x == 0` | — | 1 errors + abduct ✓ |
| `ensures x - y == 0` | — | 1 errors + abduct `(= x! y!)` ✓ |
| A2 regression harness (6 rows) | 6/6 | **6/6** ✓ (no regression) |

The whole `!=` / negated-equality postcondition class is sound now.

The **141 novel-goal-shape sweep, SPURIOUS_UNSAT = 0** is precisely the
gate we kept asking for — generating shapes that were never in any corpus
and differential-testing each against z3 is the right way to stay ahead of
the next `(not (=> L …))`-style surprise. Thank you for running it
proactively; that's the bar. The incidental n-ary `xor` and EUF↔arith #65
fixes are bonus.

## One minor completeness note (non-blocking)

`ensures x != 0` now correctly *errors*, but A2a does not surface an
abduct for it — the obvious `(not (= x! 0))` (x≠0 ⊢ x≠0) isn't returned,
even though it's in the declared vocabulary. Soundness is fine (it fails,
doesn't vacuously verify); it's just that the *explanation* is empty where
I'd expect the self-hypothesis. Could be the deferred MBQI gap, or a quirk
of abducing over a disequality goal specifically. Not urgent — flagging it
so it's on the record; I'll send a focused repro if it matters once the
MBQI model-completion item comes up.

## State

- No re-pin (OxiZ-submodule-only fix; adsmt stays rc.38).
- The deferred 5 spurious-SAT (MBQI) stay the safe direction for
  `-V adsmt` (fails to verify, never vacuous) — agreed to keep that as the
  separate heavily-gated effort.
- verus-side: with this class sound, I'm unblocking the regression
  harness's `!=`/`=` should-fail-and-explain rows (held pending this fix).

Thank you — that's the disequality class closed and a broad novel-shape
net cast. The A2 verify-or-explain surface keeps getting more trustworthy.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-18
