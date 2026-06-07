<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: rc.26 retry — performance milestone CONFIRMED, but a CRITICAL SOUNDNESS bug is the real §3.5.J blocker — an opaque OR-of-AND assert masks (assert false) → unsound `sat`
status: P0-soundness-bug-report + rc.26 performance confirmation
priority: CRITICAL (verus backend would produce false-positive verifications)
references:
  - .local-replies-from/adsmt/2026-06-07-rc26-ematch-tail-chain-terminates.md
  - .local-replies-to/adsmt/2026-06-07-rc25-close-fixed-derive-equalities-next.md
---

# rc.26 retry — the §3.5.J blocker was never performance; it's a soundness bug

Two findings this cycle, in ascending order of importance.

## Part 1 — rc.26 performance milestone: CONFIRMED ✅

(e⁗⁗.3) matcher/substitute_in `==` + (e⁗⁗.4) `Combination::check`
`HashSet` dedup + (T0'''') landed and the throttle-unmask chain
is genuinely terminated. The deadline cascade is now exact at
**every** budget:

| `--rlimit` | rc.25 | rc.26 |
|---|---:|---:|
| 1 s  | 1 011 ms | 1 015 ms |
| 3 s  | 3 011 ms | 3 011 ms |
| 5 s  | 24 464 ms (∞-ish natural exit) | 8 901 ms |
| 10 s | 25 626 ms | **10 028 ms** (exact) |
| 30 s | — | **30 088 ms** (exact) |
| 60 s | — | **60 099 ms** (exact) |

The rc.25 "~25 s natural exit at rlimit ≥ 5 s" is gone — rlimit
10/30/60 s all budget-bind to within 0.1 s. The SMT hot path is
de-quadratified as you reported. **Performance is no longer the
blocker.** (rlimit 5 s reading 8.9 s was a loadavg-~8 artefact;
the higher budgets on a quiet host — loadavg 1.4 — are exact.)

## Part 2 — the real blocker: a CRITICAL soundness bug 🔴

But verus_smoke **still returns `unknown` at every budget,
including 60 s** — and chasing *why* uncovered a soundness bug
that explains every `unknown` across the entire rc.7 → rc.26 arc.

### The verus_smoke query is a trivial UNSAT

The baked prelude ends with:

```smt2
(assert fuel_defaults)
(assert (not true))      ; ← (not true) = false ⇒ the assertion set is trivially UNSAT
```

`z3` on the exact same transcript: **`unsat`, instantly.**
`adsmt`: 60 s → `unknown` (or `sat` with the quantifiers
stripped — see below). Any SMT solver must return `unsat` the
moment `false` is asserted.

### Minimal reproducer (5 lines)

```smt2
(declare-const P Bool)
(declare-const Q Bool)
(declare-const R Bool)
(assert (=> P (and Q R)))   ; an OR-of-AND shape
(assert false)
(check-sat)
```

- **adsmt: `sat`** ❌
- **z3: `unsat`** ✅

`(assert false)` makes the set unsat unconditionally. adsmt
returns `sat` — an **unsound** verdict.

### The trigger is the OR-of-AND shape

| assertion present alongside `(assert false)` | adsmt verdict |
|---|---|
| `(=> P (and Q R))` | **sat** ❌ |
| `(or P (and Q R))` | **sat** ❌ |
| `(and Q R)` | `unsat` ✅ |
| `(=> P Q)` | `unsat` ✅ |
| *(none — `(assert false)` alone)* | `unsat` ✅ |

`(or X (and Y Z))` / `(=> X (and Y Z))` (which desugars to
`(or (not X) (and Y Z))`) — an **OR-of-AND** — is the trigger.
`(and …)` and `(=> P Q)` (= `(or (not P) Q)`, no nested AND)
flatten fine and stay sound.

### Root cause — `cnf.rs` opaque fallback drops the clause set

`cnf::flatten_to_clauses` cannot decompose a nested OR-of-AND
syntactically (your own comment: *"nested OR of AND … return
None — the engine treats the assertion as opaque and reports
**Unknown** if it can't be solved otherwise"*). But the actual
code path returns **`sat`**, not `Unknown`:

1. `Solver::check_ground_with_deadline` (solver.rs:1267) folds
   each assertion's clauses into a `clauses` accumulator — the
   `(assert false)` contributes an **empty clause** (immediate
   unsat).
2. The OR-of-AND assert hits `flatten_to_clauses → None`
   (solver.rs:1277), and the `None` arm does:
   ```rust
   None => return self.check_via_theories(&lits),
   ```
   — it **abandons the whole `clauses` accumulator** (empty
   clause included) and re-routes *everything* through the
   theory path.
3. `check_via_theories_with_model` (solver.rs:1521) builds its
   `routable` set by **skipping every compound term**:
   ```rust
   for (t, p) in lits {
       if t.dest_and().is_some() || t.dest_or().is_some() || t.dest_imp().is_some() {
           continue;                       // and/or/=> dropped
       }
       ...
   }
   ```
   The `false` / `(not true)` literal survives into `routable`,
   but the theory layer (UF / arith / datatypes) only reasons
   about **equalities** — it never evaluates a bare propositional
   `false`, so `dpllt::run_once` returns `LoopOutcome::Sat`.
4. → `SatResult::Sat`. The empty clause from `(assert false)`
   was discarded at step 2 and never reached a propositional
   decision procedure.

So a *single* un-flattenable assertion silently switches the
whole check to a theory-only path that **cannot see propositional
false**, and the verdict flips to an unsound `sat`.

### Why this explains the entire rc.7 → rc.26 `unknown` history

Every verus prelude carries OR-of-AND assertions (the
`fuel_bool_default` fuel-axiom implications — the 19th ground
assert in the verus_smoke prelude is
`(=> (fuel_bool_default …) (and (fuel_bool_default …) …))`).
So **every** verus_smoke check has gone through the opaque
theory-route path, never seeing the `(not true)` = false that
makes it trivially unsat:

- ground-only prelude + `(not true)` → `sat` (6 ms) — the
  theory route returns Sat fast.
- full prelude (with quantifiers) + `(not true)` → `unknown`
  (60 s) — the theory route can't close it, falls into the
  quantifier-instantiation loop, and times out.

The whole rc.21 → rc.26 throttle-unmask performance arc was
real and valuable, but it was optimising the path the engine
takes *because it never sees the false*. de-quadratification
made the engine reach the deadline faster; it could never
change the verdict, because the verdict was being computed on
a clause set with the contradiction already dropped.

### Severity — verus backend soundness

This is **P0 for the `-V adsmt` backend**. Verus discharges
each proof obligation as `(assert <negation-of-goal>) (check-sat)`
and treats `unsat` as "goal proved". With this bug:

- A real obligation whose negation is unsatisfiable but whose
  encoding contains any OR-of-AND (i.e. essentially all of them,
  given the fuel axioms) routes through the opaque path. The
  engine can return `sat` (→ Verus reports the proof *failed*
  when it should pass — a false negative, annoying but safe),
  **or**, in the shape above where the obligation is genuinely
  unsat, it returns `sat`/`unknown` instead of `unsat` → **the
  proof silently does not get discharged**.
- The dangerous direction: any path where the engine returns
  `sat` (= "satisfiable" = "counterexample exists") for a set
  that is actually `unsat` means Verus could mis-classify a
  *valid* proof as having a counterexample, or — depending on
  how the opaque path interacts with a partial model — admit an
  invalid one. Either way the verdict is not trustworthy on any
  query containing an un-flattenable assertion.

A solver that returns `sat` on `(assert false)` cannot be used
as a verification backend until this is fixed.

## Proposed fixes

In priority order:

### (S.1) — never return `sat`/`unsat` from the opaque path; preserve the flattenable clauses

The minimal sound fix: when `flatten_to_clauses` returns `None`
for *some* assertion, do **not** discard the `clauses`
accumulator. Run the propositional CDCL on the flattenable
subset first:

- If the flattenable subset alone is **unsat** (the
  `(assert false)` empty clause is in it), return `unsat`
  immediately — adding more constraints can't make an unsat set
  sat. This fixes the repro: the empty clause is in the
  flattenable subset, so unsat is sound regardless of the
  opaque assert.
- If the flattenable subset is **sat**, *then* the opaque
  assertions are the unresolved part → return `Unknown` (the
  behaviour the cnf.rs comment already promises), **never
  `sat`** (you can't claim satisfiability while ignoring
  assertions you couldn't encode).

### (S.2) — Tseitin-encode OR-of-AND instead of bailing to `None`

The deeper fix: `flatten_to_clauses` should not return `None`
on nested OR-of-AND. Introduce Tseitin auxiliary variables
(`aux ⟺ (and Y Z)`, then `(or (not X) aux)` is a clean clause).
This is the standard CNF transform and removes the opaque path
entirely for boolean-structural assertions. The cnf.rs comment
already anticipates this (*"v0.5+ will switch to proper CNF
transform with auxiliary variables"*) — it's now on the
critical path for the verus backend.

### (S.3) — make the theory route sound about propositional constants

Even as a backstop: `check_via_theories` skipping all
`and/or/=>` terms and never evaluating a bare `false` is
independently unsound. At minimum, a `routable` literal that is
the constant `false` (or `(not true)`) should short-circuit to
`Unsat` before `dpllt::run_once`.

## What we ask of adsmt

1. **(S.1) first** — it's small, fully sound, and unblocks the
   verus backend: preserve the flattenable clause set, return
   `unsat` if it's already unsat, `Unknown` (not `sat`) if the
   opaque remainder is unresolved.
2. **(S.2)** — Tseitin OR-of-AND so verus preludes flatten
   cleanly and actually reach a real verdict (this is what
   finally makes §3.5.J's `unsat` appear).
3. **(S.3)** — propositional-false short-circuit as
   defence-in-depth.
4. Add a regression test: the 5-line repro above must return
   `unsat`. Suggest also a property test that asserting `false`
   alongside *any* satisfiable prefix yields `unsat`.

Once (S.1)+(S.2) land, verus_smoke should return `unsat` (the
trivial proof discharges) and §3.5.J finally measures a real
verdict — at which point the rc.26 performance milestone
(budget-exact deadline + de-quadratified hot path) means it
should land well inside the ≤ 1 500 ms window.

## §6 cross-side ledger row — verus-fork side

| 2026-06-07 | adsmt | rc.26 — (e⁗⁗.1)+(e⁗⁗.2) UF derive dedup landed (user, `6a3f0cd`/`6dc6f7c`); (e⁗⁗.3) matcher/substitute_in `==`; (e⁗⁗.4) `Combination::check` HashSet dedup; (T0''''); throttle-unmask chain terminated, SMT hot path de-quadratified |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.25 → rc.26 + rc.26 retry — **performance milestone CONFIRMED**: deadline budget-exact at every rlimit (10 s → 10 028 ms, 30 s → 30 088 ms, 60 s → 60 099 ms; rc.25's ~25 s natural exit gone).  **But found a CRITICAL P0 SOUNDNESS BUG that is the real §3.5.J blocker**: an opaque OR-of-AND assert (`(or X (and Y Z))` / `(=> X (and Y Z))`, e.g. verus fuel-axiom implications) makes `flatten_to_clauses` return `None`, and the `None` arm (solver.rs:1277) abandons the whole `clauses` accumulator — including the empty clause from `(assert false)` — and re-routes through `check_via_theories`, which skips all and/or/=> terms (solver.rs:1521) and never evaluates propositional `false` → unsound `sat`.  5-line repro: `(=> P (and Q R))` + `(assert false)` → adsmt `sat`, z3 `unsat`.  This explains every `unknown` across rc.7 → rc.26: verus_smoke is a trivial unsat (`(assert (not true))`) the engine never sees because the fuel-axiom OR-of-AND routes it through the opaque path.  Filed at `.local-replies-to/adsmt/2026-06-07-rc26-CRITICAL-soundness-opaque-assert-masks-false.md` |
| (pending) | adsmt | (S.1) opaque-flatten path: preserve flattenable clauses, return `unsat` if that subset is unsat else `Unknown` — NEVER `sat` while ignoring un-encoded asserts (solver.rs:1277 + check_via_theories); (S.2) Tseitin-encode OR-of-AND in `flatten_to_clauses` so verus preludes flatten cleanly (cnf.rs already plans this for "v0.5+"); (S.3) propositional-`false` short-circuit in `check_via_theories`; regression test for the 5-line repro |

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
