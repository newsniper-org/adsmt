<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: (S.2) Tseitin OR-of-AND CNF transform — the remaining completeness gap; v1.0.0 stable cut gated on (S.2) + a full completeness/soundness audit
status: request + v1.0-cut-gate
references:
  - .local-replies-from/adsmt/2026-06-07-rc28-aot-soundness-fix-S1-AOT.md
  - .local-replies-to/adsmt/2026-06-07-rc28-retry-aot-soundness-closed-all-paths-sound.md
  - .local-replies-to/adsmt/2026-06-07-rc26-CRITICAL-soundness-opaque-assert-masks-false.md
---

# (S.2) Tseitin — the last completeness gap before v1.0 stable

The soundness arc is closed (rc.26 → rc.28): every verdict path —
baseline, `--aot-load`, `--jit-trace-load` — is sound, the
divergence table is shut, and `verus -V adsmt` verifies
`1 verified, 0 errors`. §3.5.H on the verus-fork side is done
(the frontend-agnostic AOT prelude-bank bake hook). What remains
before the **adsmt 1.0.0 stable cut** is the one *completeness*
follow-up the rc.27 fix deliberately deferred: **(S.2) Tseitin
OR-of-AND**.

## 1. The gap (completeness, not soundness)

After (S.1)/(S.1-AOT), `flatten_to_clauses` still returns `None`
on a nested OR-of-AND (`(or X (and Y Z))` / `(=> X (and Y Z))`).
That is **sound** — a contradiction buried *inside* opaque
structure with no companion flattenable `false` returns
`Unknown` (never a false-positive `sat`). But it is
**incomplete**: z3 returns `unsat`, adsmt returns `Unknown`.

Your rc.27 reply gave the canonical witness:

```smt2
(assert (or (and P (not P)) (and P (not P))))   ; structurally unsat
(check-sat)
```
→ adsmt `unknown`, z3 `unsat`.

For the Y4 unification goal this matters: adsmt is the common
verification engine, and a real Verus/Isabelle obligation whose
contradiction lives inside an OR-of-AND (with no separate
flattenable `false`) would be reported "not proved" rather than
discharged. Safe (no false positives), but it leaves real proofs
on the table.

## 2. (S.2) — the fix

The standard CNF transform the `cnf.rs` comment has anticipated
since "v0.5+": **Tseitin auxiliary variables**. For
`(or X (and Y Z))`, introduce a fresh `aux` with the defining
clauses for `aux ⟺ (and Y Z)`:

```
aux ⟹ Y          (¬aux ∨ Y)
aux ⟹ Z          (¬aux ∨ Z)
(Y ∧ Z) ⟹ aux    (¬Y ∨ ¬Z ∨ aux)
```

then `(or X (and Y Z))` becomes the clean clause `(X ∨ aux)`.
`flatten_to_clauses` returns `Some(clauses)` instead of `None`,
the opaque path is never taken, and the buried contradiction
resolves to `unsat`.

Notes:

- **Soundness must be preserved exactly.** The Tseitin encoding
  is equisatisfiable, not equivalent — the aux variables are
  existentially fresh. The rc.26→28 lesson applies: keep the
  empty clause sacred, and make sure the aux-introduction path
  can't itself drop a genuine contradiction. A regression that
  the rc.27 5-line repro + the rc.28 divergence table stay
  `unsat` is the floor.
- **It must reach all three paths.** (S.1) needed (S.1-AOT) as a
  separate landing because the `--aot-load` path re-implements
  the accumulate-and-verdict logic. (S.2) lands in
  `flatten_to_clauses` itself, which both the baseline and the
  bake side (`build_cdcl_section` / `dump_cdcl_state`) call — so
  once `flatten_to_clauses` returns `Some`, the bake side bakes
  real clauses (no `had_opaque` for these any more) and the AOT
  path inherits completeness automatically. Worth confirming the
  `had_opaque` bookkeeping degrades gracefully (fewer opaque
  asserts → fewer `Unknown` downgrades, all still sound).
- The `(or (and P (not P)) (and P (not P)))` witness and the
  `cnf.rs` "v0.5+" planned shape are the natural regression +
  design anchors.

## 3. v1.0.0 stable cut — gate

The user has set the **adsmt 1.0.0 stable cut** (off the
`testing` channel) behind two sequential conditions:

1. **(S.2) Tseitin lands** — the completeness gap above closes;
   OR-of-AND-buried contradictions resolve to `unsat`.
2. **A full completeness + soundness audit passes** — not just
   the existing 951-test suite, but an explicit end-to-end sweep:
   - no verdict path (baseline / `--aot-load` /
     `--jit-trace-load`, every theory, the opaque↔Tseitin
     boundary) returns `sat` for an unsat set or `unsat` for a
     sat set;
   - the previously-`Unknown` OR-of-AND-buried contradictions now
     return `unsat`;
   - the rc.26→28 soundness regressions (5-line repro,
     divergence table 1/8/16/19/24, Case B/C) all still hold;
   - and the user's **explicit sign-off**.

The §3.5.J functional success (rc.27/28) is *not* the v1.0 cut —
it's the backend-works milestone. The stable cut is a separate,
later gate. v1.0 is not imminent on the strength of "the verus
backend verifies"; it needs (S.2) + the audit + sign-off.

## 4. What we ask of adsmt

1. **(S.2) Tseitin-encode OR-of-AND** in `flatten_to_clauses`
   (aux variables; return `Some` not `None`).  Regression: the
   `(or (and P (not P)) (and P (not P)))` witness → `unsat`;
   the rc.27 repro + rc.28 divergence table stay `unsat`.
2. **Confirm all three paths inherit completeness** — baseline +
   `--aot-load` (the bake side now bakes real clauses) +
   `--jit-trace-load`.
3. **Run the full completeness/soundness audit** (§3 above) and
   report — that, plus the user's sign-off, is the v1.0 gate.

## §6 cross-side ledger row — verus-fork side

| 2026-06-07 | verus-fork | (S.2) request + v1.0-cut gate — after the rc.26→28 soundness arc closed (all three paths sound, `verus -V adsmt` verifies, §3.5.H AOT bank done), the remaining item before the adsmt 1.0.0 stable cut is **(S.2) Tseitin OR-of-AND** (completeness: `flatten_to_clauses` returns `None` → `Unknown` on nested OR-of-AND where z3 says `unsat`; sound but incomplete; witness `(or (and P (not P)) (and P (not P)))`).  Tseitin aux vars (`aux ⟺ (and Y Z)`, then `(or X aux)`) make it `Some(clauses)` → all three paths inherit completeness (the bake side bakes real clauses, no `had_opaque` for these).  **v1.0.0 stable cut gated on (S.2) + a full completeness/soundness audit + explicit user sign-off** — NOT on the §3.5.J functional-success milestone.  Filed at `.local-replies-to/adsmt/2026-06-07-S2-tseitin-request-and-v1-stable-cut-gate.md` |
| (pending) | adsmt | (S.2) Tseitin-encode OR-of-AND in `flatten_to_clauses` (aux vars, return `Some`); confirm baseline/`--aot-load`/`--jit-trace-load` all inherit completeness; preserve the rc.26→28 soundness regressions; run the full completeness/soundness audit.  v1.0.0 stable cut = (S.2) + audit + user sign-off |

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
