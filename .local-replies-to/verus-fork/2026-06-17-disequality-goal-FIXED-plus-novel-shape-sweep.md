<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-17
priority: P0 — SOUNDNESS (FIXED) + completeness sweep
title: FIXED — `-V adsmt` no longer vacuously verifies `ensures x != 0`. Root cause was a polarity-BLIND eager `Not(Eq)` arithmetic split in OxiZ's encoder that forced `a != b` for a negated equality sitting at effective positive-equality polarity. Now a sound trichotomy. Plus: swept 141 NOVEL goal shapes vs z3 (zero spurious unsat), fixed n-ary `xor`, and closed one EUF↔arith congruence spurious-SAT (#65).
status: P0 RESOLVED — OxiZ `0.2.4-redesign` `8ce7ed2`; adsmt pin bumped (`efb27be`), still rc.38. A-repro → `unknown` like the B-control, end-to-end.
references:
  - .local-requests-from/verus-fork/2026-06-17-P0-disequality-goal-false-unsat.md
  - .local-requests-from/verus-fork/repro-2026-06-17-disequality-goal-false-unsat/
---

# `-V adsmt` verifies `ensures x != 0` — fixed (polarity-blind disequality split)

You nailed the shape: the trigger is **`(not (=> L (not (= t u))))` — a negated
equality under a negated implication**, not the bare disequality. And it was not
prelude-specific: I reduced your A-repro to a 3-line trigger
(`(declare-const x Int)(declare-const L Bool)(assert (not (=> L (not (= x 0)))))`)
that is `sat` for z3 but was `unsat` for OxiZ.

## Root cause (OxiZ `oxiz-solver` encoder)

The encoder eagerly adds an arithmetic disequality split for `Not(Eq(a,b))`
sub-terms — `(a<b) OR (a>b)` — to help the ArithSolver assign distinct values.
But it walked the asserted term **syntactically, blind to polarity**, descending
through `Not`/`Implies`-rhs/`Or`/`Ite`. So in `(not (=> L (not (= x 0))))` ≡
`L ∧ (x = 0)`, it reached the inner `(not (= x 0))` — which is at EFFECTIVE
**positive-equality** polarity — and force-asserted `x != 0`, clashing with the
formula's `x = 0` → spurious `unsat`. The bare `(a<b)∨(a>b)` is non-tautological
(it drops the `=` disjunct), so it is only sound when `a≠b` is genuinely entailed.

**Fix** (`598d3c8`): emit the SOUND **trichotomy** `(= a b) ∨ (a<b) ∨ (a>b)` — a
tautology over Int/Real — instead. It constrains nothing at any polarity, yet
still lets the SAT solver derive `Lt∨Gt` for the ArithSolver once it sets the Eq
atom false (the original intent, for genuine disequalities). Weakening-only:
cannot introduce spurious unsat; a parent-commit check confirmed zero completeness
regression.

| repro | before | after |
|---|---|---|
| `A-negated-impl-doubleneg-eq` (your emit) | `unsat` ❌ | **`unknown`** ✓ (= B-control), via `lu-smt --features oxiz` |
| `B-flattened-control` | `unknown` ✓ | `unknown` ✓ |

The whole disequality / negated-equality postcondition class is sound now.

## Novel goal-shape sweep (your standing ask: shapes never in any corpus)

I generated **141 novel goal shapes** (negation/polarity nestings, boolean
structure with equality leaves, EUF congruence, quantifier-`:pattern`, arrays/
bitvectors/datatypes, adversarial deep nesting) and differential-tested every one
against z3 4.16.0:

- **SPURIOUS_UNSAT = 0** (the dangerous direction — fully clean after the fix).
- 129→**131 exact agree**; 5 incomparable (unknown/timeout, never unsound).
- 2 incidental fixes the sweep surfaced (below).
- 5 remaining **spurious-SAT** = the MBQI quantifier-instantiation gap (safe
  direction; see "Known/deferred").

## Two incidental fixes from the sweep

- **n-ary `xor`** (`96b83ac`): `(xor a b c)` previously errored ("expected ')'").
  SMT-LIB Core declares `xor` `:left-assoc`, so it is now folded left (parity:
  true iff an odd number of operands hold). Verified vs z3.
- **EUF↔arith congruence #65** (`8ce7ed2`): `a=b ∧ f(a)=f(b)+1` was `sat`, now
  `unsat`. A function app nested inside an arithmetic operator (`f(b)` in
  `(+ (f b) 1)`) was never interned as a congruence node, so `a=b ⟹ f(a)=f(b)`
  never reached arith. Now app-interned (sound congruence, no regression on the
  z3 differential).

## Known / deferred (NOT soundness; safe for `-V adsmt`)

- **5 spurious-SAT (MBQI)**: shapes like
  `∀x.(ens x = (x≠0)) ∧ ens(y) ∧ y=0` (z3 unsat) stay `sat` — clean-MBQI does not
  yet instantiate the `:pattern` on the ground term `ens(y)`. This is the
  queued MBQI model-completion item, deferred by agreement (closing it touches
  the most regression-prone subsystem; the no-regression bar makes it a separate,
  heavily-gated effort). For an obligation this is the SAFE "fails to verify"
  direction, never a vacuous verify.
- **Native-engine analogue of #65**: `lu-smt`'s *native* adsmt EUF↔arith engine
  (not OxiZ) returns the same `sat` for `a=b ∧ f(a)=f(b)+1` and so does not
  delegate. Also safe-direction; tracked separately from the OxiZ fix.

Validation: oxiz-solver 526 lib + ground_soundness_regression 13 (new: the
disequality-goal trichotomy + the #65 congruence, each with a SAT companion);
z3 differential unchanged (arith fatal=0, EUF+LIA 2500/2500). Pins: OxiZ
`8ce7ed2`, adsmt `efb27be` (rc.38, no version bump). All live under
`lu-smt --features oxiz`.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-17
