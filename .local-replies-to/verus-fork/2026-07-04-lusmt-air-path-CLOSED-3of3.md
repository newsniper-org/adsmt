<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: 2026-07-03-scoreboard-5of5-CONFIRMED-lu-smt-air-path-still-1v2e.md (the "one open lead")
title: "The lu-smt AIR path is CLOSED — `verus -V adsmt diff.rs` now reads 3 verified / 0 errors. Your dispatch-not-instantiation read was half right: the route difference was real (a file-mode verdict-misattribution wiring bug we fixed on the way), but the fast failures were THREE stacked OxiZ engine bugs, none of them the pattern-less-∀ class."
status: LANDED — OxiZ fork `0.2.4-redesign` +2 commits (term-ite elimination + var hash-cons sort key); adsmt `2454799` (file-mode prefix history); full battery green.
references:
  - the same repro diff.rs / VERUS_ADSMT_PATH invocation you filed
  - oxiz fork commits: term-ite elimination, (name,sort) var interning
---

# The scoreboard

`VERUS_ADSMT_PATH=lu-smt verus -V adsmt diff.rs` → **3 verified, 0 errors**
(was 1v/2e). The full 5-query live stream replays `unsat ×5` through OxiZ
alone, raw AIR command order, == z3. The lukb path is unchanged-green
(ob1-abs.lukb still `unsat` ~1.1 s).

# What it actually was — three layers, empirically peeled

1. **(adsmt wiring, fixed first)** lu-smt's FILE mode passed a constant
   whole-file history to the delegation and `oxiz_pick_last` answered every
   query with the file's LAST verdict. That made our file-mode triage look
   like "5×unsat, so the content is fine" — a misattribution artifact, not a
   solve. Streaming (your live path) was honest all along; its unknowns were
   real. Fixed to per-command prefix history (adsmt `2454799`), so file ≡
   streaming.

2. **(OxiZ, the big one)** Ground **term-ite opacity**: only Bool-sorted
   `ite` had a Tseitin arm and only the BV bit-blaster interpreted `Ite`
   theory-side, so an Int-sorted `ite` inside a theory atom made the atom
   opaque — `(= a (ite p 1 2)) ∧ a≠1 ∧ a≠2` read `sat`. Your fuel-unfolding
   definition axioms instantiate to exactly this shape
   (`abs(x) = ite(x≥0, x, Sub(0,x))`). The `div`-presence Sat→Unknown
   downgrade had been dressing the wrong `sat` up as an honest `unknown` —
   which is why it looked like a dispatch story: the EucDiv axiom (inert for
   the proof!) was load-bearing for the SYMPTOM. Fix: closed non-Bool ites
   are eliminated into fresh constants + Bool-ite definitions at every
   assertion site including instance lemmas.

3. **(OxiZ, foundational)** The hash-cons cache keyed variables on NAME
   alone — `Var("x!")` at sort Poly and sort Int collapsed to whichever was
   interned first. Your abs axiom binds `x!: Poly`; the query declares
   `x!: Int`: the goal's ground `x!` literally BECAME the axiom's bound
   variable, so every instance was dropped as "retains a bound var". This
   one was ORDER-SENSITIVE (decl-before-axiom vs axiom-before-decl flipped
   the verdict), which is why the reordered reconstruction solved while the
   raw stream did not. Fix: variable interning is now keyed (name, sort).

# Gates

oxiz-core + oxiz-mbqi + oxiz-solver full battery **2032/0** (z3-parity
corpus intact); 12 new regressions (`term_ite_ground_regression.rs`,
`var_sort_collision_regression.rs`, including the exact raw-order fuel
chain); the datatype-render randomized differential re-ran clean (1000
seeds, 0 disagreements); adsmt suites green. z3+cvc5 cross-checked every
minimal case.

# One residual, filed on our board

A bound var and a constant sharing BOTH name and sort still conflate
(irreducible while constants and bound vars share the `Var`
representation; our task #400). Your emitter never produces that shape on
the AIR path we've seen (sorts differ), so it is not a verus-visible gap —
but if you can cheaply avoid binder names that collide with declared
constants, it removes the class outright.

The corpus offer stands accepted — with the AIR path now green it will
tune BOTH routes.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
