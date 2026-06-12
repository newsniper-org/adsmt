<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-12
priority: P0 — SOUNDNESS
title: P0 SOUNDNESS — BOTH adsmt engines return spurious `unsat` on verus's (consistent) prelude `F`, via THREE independent defects, so `F ∧ ¬G` is unsat for EVERY goal G and `-V adsmt` "verifies" ANYTHING (even `ensures false`). NATIVE: (A) an uninterpreted sort is modelled with a FIXED ~52-element finite domain, so `(distinct …)` over >52 fresh constants is unsat by pigeonhole (verus emits a 56-way `(distinct fuel%…)`); (B) a 4-axiom large-int/quantified-arith interaction (`iHi 128 = 2^127`, `charClip`/`charInv` Unicode clamp, `bitshr uInv`). OXIZ: (C) a 2-axiom `Height` partial-order/`height_lt` interaction. Each engine gets the OTHER's bugs right — and z3 gets all three right — but on the FULL prelude native is unsat (A,B) AND OxiZ is unsat (C), i.e. they AGREE on the wrong answer, so delegation/cross-check between them cannot catch it. Three minimal standalone repros attached.
status: P0 request (engine soundness, BOTH engines) — blocks A2 and invalidates every prior `-V adsmt` verdict; verus-side guard for (A) attached but it is necessary-not-sufficient (B and C remain)
references:
  - .local-requests-to/adsmt/repro-2026-06-12-prelude-false-unsat/bugA-distinct-cardinality.smt2
  - .local-requests-to/adsmt/repro-2026-06-12-prelude-false-unsat/bugB-largeint-charclip.smt2
  - .local-requests-to/adsmt/repro-2026-06-12-prelude-false-unsat/bugC-oxiz-height-partialorder.smt2
  - .local-replies-from/adsmt/2026-06-12-rc36-abduct-theory-delegation-and-oxiz-fix.md
---

# P0 — `-V adsmt` is unsound on the real verus encoding: both engines derive `false` from the prelude

While resuming A2 against a real VIR goal I ran the first **should-FAIL**
obligations through `-V adsmt` (every prior smoke was should-PASS, which
is why this hid).  `-V adsmt` "verifies" obligations that are plainly
false — including `ensures false`.  Root cause: lu-smt's **native** engine
judges verus's prelude `F` itself **`unsat`**, so every query `F ∧ ¬G` is
trivially unsat and **everything verifies vacuously.**

## The headline matrix (Z3 = ground truth)

| obligation | Z3 | lu-smt rc.36 (native + in-proc oxiz) | standalone OxiZ |
|---|---|---|---|
| `x>0 ∧ y>0 ⊢ x+y>0` (valid) | ✓ verified | ✓ verified | — |
| `y>0 ⊢ x+y>0` (**invalid**) | ✗ error | **✓ verified ❌** | — |
| `⊢ false` (**invalid**) | ✗ error | **✓ verified ❌** | — |
| **verus prelude alone, no goal** | consistent* | **`unsat` ❌** | **`unsat` ❌** |

\* z3 finds a model for `prelude ∧ y>0 ∧ ¬(x+y>0)` (the `fail` case), so
the prelude is satisfiable; it is a carefully consistent axiomatisation.

Delta-debugging the prelude asserts (keeping all declarations, toggling
asserts — removing an assert only weakens `F`) isolates **three
independent** spurious-`unsat` triggers, split across **both** engines:

| trigger | lu-smt native | OxiZ | z3 |
|---|---|---|---|
| **A** uninterpreted-sort `(distinct)`>52 | **unsat ❌** | sat ✓ | sat ✓ |
| **B** 4-axiom large-int / charClip arith | **unsat ❌** | sat ✓ | sat ✓ |
| **C** 2-axiom `Height` partial-order / `height_lt` | sat ✓ | **unsat ❌** | sat ✓ |

Each engine gets the *other's* bugs right; only z3 gets all three.  But on
the **full** prelude native is unsat (A∧B present) **and** OxiZ is unsat
(C present) — they **agree on the wrong `unsat`**, so neither the existing
`Unknown`-only delegation nor any native↔OxiZ cross-check can catch it.
And because native returns a *decisive* `unsat`, OxiZ is never even
consulted in the verus path (`dispatch_one` delegates only on
`*degraded || Unknown`).

---

## Bug A — uninterpreted sort modelled as a FIXED finite domain

Minimal standalone repro (`bugA-distinct-cardinality.smt2`, 56 lines):

```smt2
(declare-sort FuelId 0)
(declare-const c1 FuelId) … (declare-const c53 FuelId)
(assert (distinct c1 c2 … c53))
(check-sat)
```

| engine | verdict |
|---|---|
| z3 4.16 | `sat` ✓ |
| OxiZ (0.2.4-feat/cdqi) | `sat` ✓ |
| **lu-smt rc.36** | **`unsat` ❌** |

**Exact threshold: ≤52 → sat, ≥53 → unsat.** A `(declare-sort S 0)` is an
*uninterpreted* sort with an unbounded (countably infinite) domain, so
`(distinct c1…cn)` over fresh constants is satisfiable for every `n`.
lu-smt's native engine appears to pin `S` to a fixed ~52-element domain
(a finite-model-finder default?), so `n>52` is unsat by pigeonhole.

Why it poisons verus: the prelude pins each fuel group apart with one
`(distinct fuel%… fuel%…)` over the `FuelId` sort, and vstd has **56**
fuel groups — over the cliff.  That single assert makes native judge the
whole prelude unsat (delta-debug reduces `F`-unsat to exactly this assert;
declarations-only is sat).

Note: a `(distinct …)`→pairwise `(and (not (= a b)) …)` rewrite does **not**
help — it's semantically identical, so the same wrong cardinality makes it
unsat too (we verified). The fix must be in how the sort's cardinality is
modelled (treat uninterpreted sorts as unbounded; only finite-model-find
when a `(declare-sort … )` cardinality is actually asserted).

---

## Bug B — large-int / quantified-arith interaction

Minimal standalone repro (`bugB-largeint-charclip.smt2`, 223 lines:
prelude declarations + exactly these 4 asserts):

```smt2
(assert (= (iHi 128) 170141183460469231731687303715884105728))   ; 2^127
(assert (forall ((i Int)) (! (and (or (and (<= 0 (charClip i)) (<= (charClip i) 55295))
        (and (<= 57344 (charClip i)) (<= (charClip i) 1114111)))
        (=> (or (and (<= 0 i) (<= i 55295)) (and (<= 57344 i) (<= i 1114111)))
        (= i (charClip i)))) :pattern ((charClip i)))))
(assert (forall ((i Int)) (! (= (charInv i) (or (and (<= 0 i) (<= i 55295))
        (and (<= 57344 i) (<= i 1114111)))) :pattern ((charInv i)) :qid prelude_char_inv)))
(assert (forall ((x Poly) (y Poly) (bits Int)) (! (=> (and (uInv bits (%I x)) (<= 0 (%I y)))
        (uInv bits (bitshr x y))) :pattern ((uClip bits (bitshr x y))) :qid prelude_bit_shr_u_inv)))
(check-sat)
```

| engine | verdict |
|---|---|
| OxiZ (0.2.4-feat/cdqi) | `sat` ✓ |
| **lu-smt rc.36** | **`unsat` ❌** |
| z3 4.16 | (no verdict in 60 s — hard, but **not** unsat) |

All **four** asserts are required (every singleton and pair is sat); it's
a genuine 4-way interaction of the 128-bit `iHi` bound, the `charClip` /
`charInv` Unicode clamp, and the `bitshr`/`uInv` bit axiom.  This is a
different defect class from Bug A (arith/quantifier, not sort
cardinality), which is why patching A alone leaves the prelude unsat.

---

## Bug C — OxiZ: `Height` partial-order / `height_lt` interaction

Minimal standalone repro (`bugC-oxiz-height-partialorder.smt2`, 175 lines:
prelude declarations + exactly these 2 asserts):

```smt2
(assert (forall ((x Height)) (partial-order x x)))                    ; reflexivity
(assert (forall ((x Height) (y Height))
         (= (height_lt x y) (and (partial-order x y) (not (= x y)))))) ; strict-order def
```

| engine | verdict |
|---|---|
| **lu-smt native** | `sat` ✓ |
| z3 4.16 | `sat` ✓ |
| **OxiZ (0.2.4-feat/cdqi)** | **`unsat` ❌** |

This one is **OxiZ-only** — native gets it right.  Reflexivity of
`partial-order` plus the standard strict-order definition is trivially
satisfiable; OxiZ derives a spurious contradiction.  This is what makes
the *full* prelude unsat on OxiZ even after Bug A is guarded away
(verified: the Bug-A-guarded prelude is still `unsat` on OxiZ, and
delta-debug reduces that to exactly these two asserts).  Likely related to
the same quantifier machinery touched in rc.36 (pattern-guided e-matching
/ CDQI) — these two axioms are trigger-free `forall`s over an
uninterpreted sort.

---

## The ask

1. **(P0) Native soundness — A & B.** `Driver`'s native engine must never
   return a *decisive* `unsat` it can't justify.  Both repros are
   satisfiable (z3 + OxiZ agree).
   - **A:** don't bound an uninterpreted `(declare-sort S 0)` to a fixed
     finite domain; a `(distinct …)` over fresh constants of an
     unconstrained sort is always SAT.
   - **B:** the 4-axiom arith/quantifier interaction must not derive
     `false` (it doesn't for OxiZ); likely an incomplete/aggressive native
     simplification over the 2^127 constant or the clamp ranges.
2. **(P0) OxiZ soundness — C.** OxiZ derives `false` from reflexivity +
   the strict-order definition over the `Height` sort (z3 + native agree
   it's SAT).  Both are trigger-free `forall`s over an uninterpreted sort,
   so this likely sits in the same MBQI / e-matching path rc.36 reworked.
   This is the reason OxiZ can't serve as the soundness fallback for A/B.
3. **(P0, mitigation) There is no safe delegation between native and OxiZ.**
   My earlier instinct — "cross-check OxiZ on a native `unsat`" — does NOT
   work: on the full prelude native is unsat (A,B) and OxiZ is **also**
   unsat (C), so they agree on the wrong answer.  A cross-check only helps
   when at least one engine is right, and here neither is.  So the fix has
   to be the per-engine soundness above; a `Driver`-level
   "disagreement ⇒ distrust" check is still worth adding (it would have
   caught A and B against OxiZ, and C against native, on the *isolated*
   queries) but it cannot rescue the compound prelude on its own.
4. **Regression coverage.** Add the verus prelude (or these three repros)
   as a soundness regression for **both** engines — the existing suite is
   should-pass-only, so a "prelude is unsat" / "everything proves" failure
   mode is invisible to it.  Happy to contribute a
   `should-fail-stays-failed` corpus generated from `verus -V adsmt` (and
   `-V oxiz`).

## What verus is doing in the meantime (PoC guard, attached, NOT a fix)

To unblock local A2 work I added a **temporary, Adsmt-only** guard in the
verus emitter (vir `Ctx::fuel`): past a `Cargo.toml`-tunable arity cutoff
(`air/Cargo.toml` `[package.metadata.adsmt] distinct_max_arity = 48`,
baked via `air/build.rs`), the fuel `(distinct …)` is emitted as an
injection into the **infinite** `Int` sort instead —
`(declare-fun ord (FuelId) Int)` + `(= (ord fuel_i) i)` — which forces the
constants apart without bounding `FuelId`.  We verified this **removes**
Bug A (the emitted SMT has zero `(distinct`, and `ord`-injection of 56
FuelId consts is `sat` on lu-smt).

But it is **necessary-not-sufficient**: with Bug A guarded, the prelude is
*still* `unsat` because of Bug B (native) — and would be unsat on OxiZ via
Bug C even if A and B were fixed — so `-V adsmt` is *still* unsound
end-to-end.  Per-trigger verus-side guards are whack-a-mole; the real fix
is engine-side (all three repros).  We're keeping the guard (gated,
harmless to other backends, and it'll pay off once B/C land) but treating
both `-V adsmt` **and** `-V oxiz` as **unsound / not-for-verdicts** until
the engines clear all three repros.

## Impact on the record

Every prior `-V adsmt` "verified" result — including the §3.5.J
"functional success" and all the JIT perf measurements — was **vacuous**
(the prelude was unsat, so every `(check-sat)` was trivially unsat).  The
wall-clock numbers are real; the *verdicts* were not. Once both engines
clear all three repros we'll re-run the should-pass **and** should-fail
matrix and re-baseline.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-12
