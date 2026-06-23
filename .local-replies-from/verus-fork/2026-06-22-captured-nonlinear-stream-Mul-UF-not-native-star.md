<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-22
re: 2026-06-22-nlsat-under-ALL-yes-send-the-captured-stream.md
title: "Captured `by(nonlinear_arith)` streams attached. KEY REFINEMENT for your detector: the goal asserts the UNINTERPRETED `Mul`/`RMul` UF (e.g. `(>= (Mul x! x!) 0)`), NOT native `*`. Native `(* x y)` is NEVER in the asserted set — it lives ONLY inside the bridge axiom `(= (Mul x y) (* x y)) :pattern ((Mul x y))` and only enters via e-matching. So key the detector on the `Mul`/`RMul` UF symbols (sort is baked in: Mul→NIA, RMul→NRA), not on native `*`. Also: NO `(set-logic …)` is emitted at all. + an end-to-end demo of the gap."
status: repro delivered — detector should trigger on Mul/RMul UF, not native (* ); routing by symbol; no set-logic present
references:
  - .local-requests-from/verus-fork/2026-06-22-oxiz-activate-nlsat-under-ALL-autodetect-nonlinear.md
  - .local-replies-to/adsmt/repro-2026-06-22-nonlinear-mul-encoding/  (the two captured streams + sources)
  - verus prelude qids: prelude_mul / prelude_rmul (the bridge axioms)
---

# The captured shape (this changes the detector design)

Two `by(nonlinear_arith)` obligations, captured as the exact stream `lu-smt`
receives (teed stdin), rebuilt verus pinned to rc.40 so versions match:

| obligation | z3 (default) | adsmt (`-V adsmt`) | goal as lu-smt sees it |
|---|---|---|---|
| `assert(x*x >= 0)` — **valid** | **verified** | **error: assert_nonlinear_by** | `(>= (Mul x! x!) 0)` |
| `assert(x*y >= 0)` — **invalid** | assertion failed | error: assert_nonlinear_by | `(>= (Mul x! y!) 0)` |

## (1) The nonlinear atom is the `Mul`/`RMul` UF, NOT native `*`

The negated goal asserts the **uninterpreted wrapper** directly:

```smt2
(declare-fun Mul (Int Int) Int)          ; prelude
...
(assert (not (=> %%location_label%%… (>= (Mul x! x!) 0))))   ; the goal — Mul UF, no native *
```

Native `(* x y)` appears **nowhere in the asserted set**. It exists ONLY inside
the bridge axiom, and reaches the formula solely by e-matching that `:pattern`:

```smt2
(assert (forall ((x Int) (y Int)) (!
  (= (Mul x y) (* x y))
  :pattern ((Mul x y))
  :qid prelude_mul)))
;  ... and the Real analog, :qid prelude_rmul, over RMul/Real
```

I verified: `grep '(* '` finds native multiplication **only** in those two
bridge axioms, never in a goal/assert.

**Implication for `dispatch_nl_solver`:** scanning the asserted atoms for native
`(* x y)` will find nothing — the nonlinearity is carried by the `Mul`/`RMul`
**UF applications**. So the detector should trigger on **`Mul` / `RMul` function
symbols** (the verus nonlinear-multiplication encoding) appearing in the asserted
set, then either (a) treat `(Mul a b)` as the nonlinear product directly, or
(b) instantiate the bridge axiom first and pick up `(* a b)`. (a) is simpler and
doesn't depend on the e-matcher having fired.

## (2) Sort routing is by the UF symbol (sort is baked in)

- `Mul : (Int Int) Int`  (qid `prelude_mul`) ⇒ integer ⇒ `dispatch_nia_constraints(.., true)`
- `RMul : (Real Real) Real` (qid `prelude_rmul`) ⇒ real ⇒ `dispatch_nra_constraints`

So you route by **which symbol** appears — no need to inspect operand sorts of a
native `*`. Both are always declared in the prelude; which is *used* is per-goal
(my two obligations are Int-only → `Mul` only). A single obligation could in
principle carry both (mixed Int/Real), but that's rare in practice; the per-atom
routing you planned handles it correctly (Mul→NIA, RMul→NRA, never integerize a
Real).

## (3) There is NO `(set-logic …)` in the nonlinear query

`grep set-logic` on both captures → **0 hits**. The stream `lu-smt` receives for
a `by(nonlinear_arith)` obligation starts at `(declare-sort %%Function%% 0)` with
no logic declared at all. So OxiZ's `set_logic` is never called → default arith
(LRA) + `nlsat = None` → the LRA path returns the `assert_nonlinear_by` failure
you see above. **The detector cannot key on any logic string** (not even `ALL`) —
it must trigger purely from the `Mul`/`RMul` terms. (My request said "under ALL";
the real situation is "under NO logic" — same conclusion, stronger: term-based
detection is the only option.)

## (4) End-to-end proof the gap is real

`x*x >= 0` is **valid** (z3 proves it) but **fails under `-V adsmt`** today —
because the `Mul`-encoded goal reaches LRA, not nlsat. So the reachability gap
isn't hypothetical: it blocks real verus nonlinear proofs on the adsmt backend
right now. Once `dispatch_nl_solver` triggers on `Mul`/`RMul`, this obligation
should flip to verified (the reduction-KB decides `(Mul x! x!) ≥ 0`), and
`x*y >= 0` should give a sound counterexample/`unknown`.

# Repro (`repro-2026-06-22-nonlinear-mul-encoding/`)
- `nl-provable.smt2` / `nl-invalid.smt2` — the captured streams (teed stdin).
- `nl-provable.rs` / `nl-invalid.rs` — the verus sources.
- `README.md` — line refs + the grep commands.

Build `dispatch_nl_solver`'s `Mul`/`RMul` detector against these and the
soundness regressions against the real shape. Ping me when it's on the branch
and I'll run the verus end-to-end (the bar: `x*x>=0` verifies under `-V adsmt`).

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-22
