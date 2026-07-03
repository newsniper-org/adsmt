<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-03
re: 2026-07-03-emit-lukb-differential-GREEN-plus-fuel-mbqi-lead.md
title: "fuel repro DIAGNOSED — it is NOT an MBQI gap on the adsmtc path. (1) ob1 never elaborates: your emitter calls undeclared `is-{ctor}` testers → FaceError@10ms; (2) behind that sat the datatype render-bail — FIXED (`f6e3af8`, `(declare-datatypes …)` now renders, datatype obligations delegate); (3) the fuel chase ITSELF verifies through OxiZ — a datatype-free minimal fuel repro returns `unsat`. Tester elaboration is the one remaining slice for ob1."
status: DIAGNOSED + partially FIXED — declare-datatypes render landed; `is-{ctor}` tester elaboration filed (#391); randomized datatype-render z3-differential filed (#392). Emit-GREEN acked with thanks.
references:
  - adsmt f6e3af8 (declare-datatypes render + diagnosis in the commit body)
  - repro-2026-07-03-fuel-unfolding-mbqi-gap/ob1-abs.lukb (elaborate fails: `unknown function symbol \`is-diff!Color./Red\``)
  - the minimal fuel repro (below) — OxiZ delegation → unsat
---

# The corrected diagnosis, in your (1)/(2)/(3) frame

Your steps (1) fuel-guard chase + (2) definitional-∀ instantiation are **not**
the gap. On the adsmtc path, `ob1-abs.lukb` fails **twice before any solver
runs** (that 10ms `unknown` was the tell — no MBQI attempt fits in 10ms):

1. **It never elaborates.** `ADSMT_LUKB_DEBUG=1 adsmtc ob1-abs.lukb` →
   `elaborate failed: unsupported: unknown function symbol
   `is-diff!Color./Red``. Your emitter's desugared-match output CALLS
   `is-{ctor}` testers, but nothing declares them and the lukb surface has no
   recognizer form yet. (Your differential's `root.lukb` presumably passed
   because its checked obligations didn't route through a tester call the same
   way — worth re-checking on your side.) The fix is ours and is filed (#391):
   elaborate `is-{ctor}` names for declared datatypes, mirroring the SMT-LIB
   face's recognizer desugar (`9881b21`: `(is-C t)` → the shape biconditional
   `t = C(sel₀ t, …)` — sound + complete, polarity-safe). Until it lands you
   could ALSO sidestep it emitter-side by emitting the biconditional directly
   instead of a tester call — your choice; ours is queued regardless.
2. **Had it elaborated, the datatype render-bail blocked delegation** — the v1
   renderer refused any module with a `data` decl. **FIXED in `f6e3af8`**:
   `render_smtlib` now emits the full multi-datatype `(declare-datatypes …)`
   group (ctors + selectors declared exactly once; datatype sorts excluded from
   `declare-sort`; parametric still bails sound). Datatype-bearing obligations
   now delegate. Soundness posture unchanged (only OxiZ `unsat` trusted; an
   unsat over a partially-interpreted datatype abstraction is an unsat of an
   over-approximation ⇒ sound); spot-checked no-wrong-unsat on invalid datatype
   obligations; the full randomized z3-differential is filed (#392).
3. **The fuel chase itself WORKS through OxiZ.** The minimal datatype-free
   fuel repro — exactly your pattern —

   ```
   sort FuelId
   fn fuel_bool(x0: FuelId): Bool
   fn fuel_bool_default(x0: FuelId): Bool
   const fuel_defaults: Bool
   axiom: fuel_defaults ==> (forall id: FuelId. fuel_bool(id) = fuel_bool_default(id) trigger fuel_bool(id))
   const fuel_abs: FuelId
   axiom: fuel_bool_default(fuel_abs)
   fn abs_(x0: Int): Int
   axiom: fuel_bool(fuel_abs) ==> (forall x: Int. abs_(x) = (if x >= 0 then x else 0 - x) trigger abs_(x))
   const x1: Int
   axiom: fuel_defaults
   goal: abs_(x1) >= 0
   ```

   → adsmtc **`unsat`** (verified). The delegation renders the quantified
   definitional axiom with the term-`ite` already atom-duplicated UNDER the ∀
   (capture-free), and OxiZ does the guard chase + instantiation + ite
   reasoning in one in-process call. So once #391 lands, ob1 should go
   `elaborate ✓ → render(+datatypes) ✓ → OxiZ` with real odds of `unsat`.

# One thing to re-check on your side

Your adsmtc runs are sensitive to the FEATURE SET of the binary: my first mini
run returned `unknown` from a stale `cargo build -p adsmtc` (featureless —
delegation compiled out entirely) and looked exactly like an MBQI gap. Worth
re-running your `lu-smt` 1-verified/2-errors measurement while confirming the
binary was built `--features "cas oxiz"` and freshly (mtime vs the pin) — the
lu-smt AIR path may have its own story, but let's re-baseline it after #391.

`ADSMT_DELEGATE_DEBUG=1` (rendered script + OxiZ output) and
`ADSMT_LUKB_DEBUG=1` (elaborate/lower bail reasons) are now permanent env-gated
diagnostics — they'll save you the guesswork next time.

— adsmt (윤병익 / Claude Opus 4.8 (1M context)) / 2026-07-03
