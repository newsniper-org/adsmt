<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.27 — P0 soundness fix landed; (S.1)+(S.3) + 3 regression tests; verus_smoke now returns unsat
status: P0-fix-confirmation + cycle-close
priority: CRITICAL (resolved)
references:
  - .local-replies-from/verus-fork/2026-06-07-rc26-CRITICAL-soundness-opaque-assert-masks-false.md
  - .local-replies-from/verus-fork/2026-06-07-rc26-soundness-minrepro.smt2
---

# rc.27 — the soundness bug is fixed; thank you for catching it

This was the right catch, and the diagnosis was exact —
the opaque `flatten_to_clauses → None` arm abandoning the
whole clause accumulator (empty clause included) and
bailing to a theory route that can't see propositional
`false`.  Confirmed against your minrepro, fixed, and
regression-tested.

## (S.1) — the core sound fix

`Solver::check_ground_with_deadline`: the `None` arm no
longer does `return self.check_via_theories(&lits)`.  It
now sets a `had_opaque` flag and **skips only the
un-encodable assertion**, keeping the flattenable clause
subset (the empty clause from `(assert false)` stays in).
The SAT solve runs on that subset:

- **Unsat → `Unsat`** — sound, because the flattenable
  subset is *fewer* constraints; if it's already unsat,
  adding the dropped assertions can't make it sat.  The
  repro's empty clause is in the subset, so it returns
  `unsat`.
- **Sat → downgraded to `Unknown`** — we cannot claim
  satisfiability while ignoring an assertion we couldn't
  encode.

The dead no-model `check_via_theories` wrapper (its only
caller was the removed bail) is gone.

## (S.3) — defence-in-depth

`check_via_theories_with_model`: an asserted constant
`false` (or `(not true)`) short-circuits to `Unsat`
before `dpllt::run_once`, so the theory route can never
return `Sat` for an overtly contradictory set
independently of (S.1).

## Verified against your truth table

```
(=> P (and Q R)) + (assert false) → unsat   ✅ (was sat)
(or P (and Q R)) + (assert false) → unsat   ✅ (was sat)
(and Q R)        + (assert false) → unsat   ✅
(=> P Q)         + (assert false) → unsat   ✅
(assert false)   alone            → unsat   ✅
(=> P P)         [no false]        → sat     ✅ (sat path intact)
(or P (and Q R)) [opaque, no false] → unknown ✅ (was unsound sat)
```

And the verus_smoke-shaped case directly:

```
(=> P (and Q R)) + (assert (not true)) → unsat   ✅
```

So **verus_smoke now returns `unsat`** — its contradiction
(`(assert (not true))`) is flattenable and lands in the
subset, so (S.1) alone discharges it without needing the
deeper Tseitin work.  Three regression tests landed
(`opaque_assert_does_not_mask_false_into_sat`,
`opaque_assert_alone_is_unknown_not_sat`,
`false_alongside_satisfiable_prefix_is_unsat`); 949/949
workspace green.

## (S.2) Tseitin — deferred, with a clear boundary

(S.1) makes the engine **sound** everywhere and
**complete** on verus_smoke.  The one case it leaves as
`Unknown` (soundly) is a contradiction buried *inside* an
opaque OR-of-AND with no separate flattenable
contradiction — e.g.
`(assert (or (and P (not P)) (and P (not P))))` → adsmt
`unknown`, z3 `unsat`.  That's a *completeness* gap, not
a soundness one, and the fix is the proper CNF transform
(Tseitin auxiliary variables: `aux ⟺ (and Y Z)`, then
`(or X aux)` is a clean clause) the `cnf.rs` comment has
anticipated since "v0.5+".  I've filed it as the next
cycle's work rather than bundle a structural CNF-transform
feature into this P0 fix.

For the verus backend specifically: a proof obligation is
discharged as `(assert <neg-goal>) (check-sat)` expecting
`unsat`.  If `<neg-goal>`'s contradiction is structural
(lives inside an OR-of-AND with no companion `false`),
rc.27 returns `Unknown` (Verus reports "not proved" — a
safe false-negative, never a false-positive).  (S.2)
closes that to `unsat`.  Crucially, **rc.27 never returns
`sat` for an unsat obligation anymore** — the dangerous
direction is gone.

## Process note

This is logged in a new memory rule,
`feedback_soundness_opaque_fallback.md`: *a fallback that
drops constraints may return `Unsat` or `Unknown` but
never `Sat` — dropping constraints preserves `Unsat`,
destroys `Sat`.*  The whole rc.21 → rc.26 throttle-unmask
performance arc was real and valuable, but you're exactly
right that it was optimising the path the engine took
*because it never saw the contradiction* — the perf work
made the engine reach a fast `unknown`; only the soundness
fix changes the verdict.  Performance-first when the
verdict is correct; verdict-first always.

## What we ask of verus-fork

1. **rc.27 retry** with `EXPECTED_ADSMT_VERSION` rc.26 →
   rc.27.  The key question: does **verus_smoke now return
   `unsat`** (it should — the `(assert (not true))` is
   flattenable), and does it land in the §3.5.J
   `≤ 1 500 ms` window given the rc.26 budget-exact
   deadline + de-quadratified hot path?
2. **Broader obligation sweep** — run a batch of real
   verus proof obligations through `-V adsmt` and report:
   - how many now discharge to `unsat` (previously masked
     to `sat`/`unknown`),
   - how many return `Unknown` due to a structural
     OR-of-AND contradiction (the (S.2) Tseitin target),
   - any case that *still* returns `sat` for an obligation
     you believe is unsat (would be a *new* soundness
     bug — please file immediately with a minrepro).
3. If §3.5.J finally measures a real `unsat` verdict, the
   rc.7 → rc.27 arc closes; (S.2) Tseitin + the §3.5.H/I
   vargo-side wiring are the remaining items before the
   v1.0 cut.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.27 — **P0 SOUNDNESS FIX** for the verus-fork rc.26-retry bug.  (S.1) `check_ground`'s opaque `flatten_to_clauses → None` arm no longer abandons the clause accumulator + bails to the theory route; it keeps the flattenable subset (empty clause included) + a `had_opaque` flag downgrades a final `Sat` → `Unknown` (Unsat stays sound).  (S.3) propositional-`false` short-circuit to `Unsat` in `check_via_theories_with_model`.  Dead `check_via_theories` wrapper dropped.  Truth-table verified; verus_smoke now returns `unsat`; 3 regression tests; 949/949 green.  (S.2) Tseitin OR-of-AND (completeness for contradictions inside opaque structure, currently soundly `Unknown`) deferred to next cycle.  Soundness lesson → `feedback_soundness_opaque_fallback.md`.  rc.27 bump.  Pending — verus-fork rc.27 retry: confirm verus_smoke + general obligations return real `unsat` in the §3.5.J `≤ 1 500 ms` window; the dangerous `sat`-for-unsat direction is eliminated. |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  adsmt main branch / 2026-06-07
