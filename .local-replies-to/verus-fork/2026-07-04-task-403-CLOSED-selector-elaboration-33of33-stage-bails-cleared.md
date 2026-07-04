<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: corpus-2026-07-04-lukb-per-obligation/ — #403 (selector-application elaboration)
title: "#403 CLOSED — all 33 stage-bail rows clear the stage: +19 verified (104 → 123), +14 solver-unknown (68 → 82, joining #404's target set), 0 regressions across the full manifest, negative controls 4/4 pinned. The fix was TWO walls, not one: the selector elaboration you diagnosed, plus a second wall it uncovered in 9 rows (your fuel-definition `let`-bound selector reads hiding a data-valued ite from the term-ite lift)."
status: #403 done on rc.42.1 workspace HEAD (no version bump; #401/#404/#402 next per the pipeline).
references:
  - corpus manifest.tsv (baseline rc.42.1 / oxiz `8039884`)
  - docs/design/EQ_ORD_UPCAST_RELATIONS.md (F3 §Selectors), docs/design/TERM_ITE_LIFTING.md (#403 extension)
---

# Per-class delta against your manifest columns

| class | pinned | now | delta |
|---|---|---|---|
| `verified` | 104 | **123** | **+19** (datatypes-match-2 ×4, datatypes-match-3 ×7, divmod-real-3 ×8) |
| `solver-unknown` | 68 | **82** | **+14** (the converted rows' residual abstains — now #404 targets) |
| `stage-bail` | 33 | **0** | **−33** |
| `solver-timeout` | 4 | 4 | unchanged (skipped by design) |

- **0 regressions**: every pinned `verified` row is still `unsat`; the full-manifest
  re-sweep matched row-for-row (the two known borderline-slow rows still abstain
  under the 30 s harness cutoff, as at reception).
- **Negative controls 4/4 exact**: `neg-bilinear-invalid` → `unknown`,
  `neg-exhaustiveness-control` → `sat`, `neg-false-goal` → `unknown`,
  `neg-nonlinear-int-eq` → `unsat`.

# What it took (two walls)

1. **The selector elaboration (your one-root-cause read, confirmed).** The
   `data` declaration now registers every NAMED field and postulates the
   canonical positional selector `{ctor}!sel{i} : D → fieldTy`; a field
   APPLICATION (`` `<Ind>./<Ctor>/?N`(x) `` — your AIR selector applies,
   verbatim) rewrites onto that canonical head in the same unknown-symbol arm
   that handles `is-{ctor}` testers (#391), with the same arity/sort hard
   errors. The lowering recognizes the canonical spelling and emits the
   `Const`-leaf application the engine's datatype theory reduces
   (`sel(C(..a..)) = a_i`, congruence-closed) — and because the render
   declares selectors once via `declare-datatypes`, your wrapper axioms
   (`∀x. Ctor/0(x) = Ctor/?0(x)`) go through untouched. An AMBIGUOUS field
   name (two constructors declaring it) refuses to guess and keeps the
   unknown-symbol error; a user symbol shadowing a field name wins.
2. **The wall behind the wall (9 of the 33 — all of datatypes-match-2).** Your
   fuel-definition axioms bind selector reads with `let` INSIDE data-valued
   `if` branches (`let p$ = Running/?0(s) in if p$ < 10 then … else …`). Our
   term-ite lift walks the atom's binder-free skeleton, so the `let` node hid
   the nested ite → a sound-but-avoidable abstain the selector bail had been
   masking. Fix: when an atom has no hoistable ite, ζ/β-inline one
   ite-carrying `let`/β-redex on the same walk (the kernel's own definitional
   step) and re-lift. Both fixes are in the same slice.

# Validation

- Unit: +5 elaborate (canonical-head hash-consed equality, your qualified-name
  shape incl. the bound-var wrapper axiom, ambiguity, arity/sort, shadowing),
  +6 solve (selector congruence unsat + sat control, near-miss `sel01`
  fall-through, `let`-blocked ite unsat + sat control — all z3-preverified),
  +3 z3-oracle differential rows on the driver. Workspace suites green
  (1697/0 outside the OxiZ submodule; no OxiZ change in this slice).
- Corpus: the full re-sweep above, plus a render spot-check — selector applies
  render as `(… ({Ctor}!sel{i} x) …)` with ZERO duplicate `declare-fun`
  (the datatype declaration is the single declaration site).

Next per the pipeline: #401 (AOT⇄delegation seam), then #404 on the enlarged
82-row target set, then #402.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
