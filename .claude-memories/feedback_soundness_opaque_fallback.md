---
name: A fallback that drops constraints must never report sat/unsat
description: When a solver path can't encode an assertion and falls back to another path, that fallback must NOT silently discard the constraints it couldn't handle and report a definite verdict. rc.27 P0 — `check_ground`'s opaque `flatten_to_clauses → None` arm re-routed through a theory path that dropped the whole clause accumulator (empty clause from `(assert false)` included), returning unsound `sat`. Rule: a path that ignored any assertion may return `Unsat` (a subset being unsat ⟹ the superset is unsat) or `Unknown`, but NEVER `Sat`.
type: feedback
---

A solver computes a verdict over a *set* of assertions.
If any code path handles only a *subset* — because it
couldn't encode the rest, hit a size bound, took a
fallback branch — then the verdict it produces is only
valid for that subset, and **the soundness of projecting
the subset's verdict onto the full set is asymmetric**:

- **`Unsat` is sound to keep.** The subset is *fewer*
  constraints than the full set; if the subset is
  already unsatisfiable, adding the dropped assertions
  (more constraints) cannot make it satisfiable.
  `subset unsat ⟹ full unsat`.
- **`Sat` is NOT sound to keep.** A model for the subset
  need not satisfy the dropped assertions.  Reporting
  `Sat` while having ignored constraints is an unsound
  claim of satisfiability.  Downgrade to `Unknown`.
- **`Unknown` is always sound** (it claims nothing).

So the discipline for *any* "can't handle this, fall
back" branch:

1. **Never discard the constraints already collected.**
   Keep solving the encodable subset.
2. **Track that something was dropped** (a `had_opaque`
   flag, an "incomplete" marker).
3. At the verdict edge: `Unsat` → return it; `Sat` →
   downgrade to `Unknown` if anything was dropped; raw
   `Unknown` → return it.

**Why:** rc.27 P0 (verus-fork rc.26 retry).
`Solver::check_ground_with_deadline` folds each
assertion's CNF into a `clauses` accumulator;
`(assert false)` contributes an empty clause (immediate
unsat).  When *any* assertion hit
`flatten_to_clauses → None` (a nested OR-of-AND the v0.3
flattener can't decompose — ubiquitous in verus fuel
axioms), the `None` arm did
`return self.check_via_theories(&lits)` — which
**abandoned the whole accumulator (empty clause
included)** and re-routed through the theory path.  That
path skips every compound `and`/`or`/`=>` term and never
evaluates a bare propositional `false`, so it returned
`Sat`.  Net: `(=> P (and Q R))` + `(assert false)` →
`sat` (z3: `unsat`).  A solver that returns `sat` on
`(assert false)` cannot back a verifier — and this had
silently masked the trivially-unsat verus_smoke fixture
(`(assert (not true))`) for the entire rc.7 → rc.26 arc,
because the fuel-axiom OR-of-AND always took the opaque
route.  The whole performance arc was optimising the
path the engine took *because it never saw the
contradiction*.

The fix (rc.27 S.1): the opaque arm sets `had_opaque` and
skips only that assertion; the SAT solve runs on the
flattenable subset; `Unsat` returns directly, `Sat`
downgrades to `Unknown`.  Plus (S.3) a propositional-
`false` short-circuit to `Unsat` in the theory route as
defence-in-depth.

**How to apply:**

- **When writing a fallback branch** (`if can't_encode {
  fall_back() }`, `match … { None => other_path() }`):
  before routing away, ask *"does the other path see all
  the constraints this one collected?"*  If not, you have
  the rc.27 shape.  Keep the collected constraints; mark
  incompleteness; gate the `Sat` verdict.
- **When reviewing a solver verdict path**, grep for
  early `return` inside the assertion / clause
  accumulation loop — each one is a candidate for "did
  this drop the accumulator?".
- **Soundness asymmetry is the load-bearing fact**:
  dropping constraints preserves `Unsat`, destroys
  `Sat`.  Any "best-effort" / "partial" / "opaque" /
  "fallback" path must encode this asymmetry explicitly.
- **A `false`-returning theory/decision path that can't
  evaluate propositional constants** is independently
  unsound — guard the constant-`false` (and
  `(not true)`) case before handing literals to a layer
  that only reasons about equalities.
- **Completeness vs soundness**: (S.1) makes the engine
  *sound* (returns `Unknown` instead of wrong `Sat`) but
  *incomplete* on obligations whose contradiction lives
  inside the un-encodable structure (it returns `Unknown`
  where `Unsat` is the truth).  The completeness fix is
  a proper CNF transform (Tseitin auxiliary variables for
  OR-of-AND) so the structure is encodable in the first
  place — rc.27 (S.2), a follow-up.  Ship the soundness
  fix first; never let an incompleteness excuse a
  soundness hole.

Regression anchors (adsmt-engine `solver.rs::tests`):
`opaque_assert_does_not_mask_false_into_sat`,
`opaque_assert_alone_is_unknown_not_sat`,
`false_alongside_satisfiable_prefix_is_unsat`.
