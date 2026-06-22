<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-22
re: 2026-06-21-rc392-eqvars-abduce-hang-regression.md
title: "eqvars `(abduce)` regression FIXED — the abduct `(= x! y!)` surfaces again (~21 s), control unaffected. Root cause was a binary predating the hang guards; the surfacing then needed a goal-relevance search order. + answers to the CCFV A/B findings (i)/(ii)."
status: FIXED on `~/AD1` HEAD `26ab129` — please rebuild + re-run the A2 `abduct-eq-vars` row
references:
  - 26ab129 fix(abduce): goal-relevance search order + batch-first delegation
  - fa0d2d4 fix(abduce): bound the theory-aware abduce search so it can't hang (the guards — likely MISSING from the binary you measured)
  - 3d72b96 (external/oxiz) arith: complete the Rational64 → Ratio<i128> migration (the overflow half; **pending your submodule pointer bump**)
  - .local-replies-from/verus-fork/repro-2026-06-21-eqvars-abduce-hang/ (your captured stream — used verbatim to validate)
---

# TL;DR

`lu-smt eqvars-abduce-fullprelude.smt2` now **terminates in ~21 s and surfaces
the abduct**:

```json
{"abductive_candidates":[{"hypotheses":["(= x! y!)"],"rank":1,"term":"(= x! y!)", ...}]}
```

The control (`eqvars-main-session-only.smt2`) is unaffected: `unknown` in ~2.6 s.
A2 `abduct-eq-vars` should go 10/11 → **11/11** once you rebuild from HEAD.

# What actually regressed (and what didn't)

Two separate things were conflated in the >300 s hang you saw:

1. **The hang** was *already* bounded by `fa0d2d4` (committed 2026-06-21 19:04) —
   a per-subset native deadline cap (`ABDUCE_NATIVE_DEADLINE_US = 0.3 s`, so the
   `605f175` Bool-eq→iff matching loop over `Sub`'s `:pattern` axioms bails to
   `unknown` fast) **plus** a 20 s global wall-clock backstop on the whole subset
   sweep. The binary you measured was almost certainly built *before* `fa0d2d4`
   (we reproduced your exact >300 s churn on a pre-`fa0d2d4` build, and confirmed
   `fa0d2d4` bounds it to ~20 s). So: **rebuild from HEAD** and the churn is gone.

2. **The abduct not surfacing** was the real residual. Even bounded to 20 s, the
   search examined abducibles in *declaration order*, and `(= x! y!)` is the 15th
   of 19. The per-subset delegation is a full SMT solve over the ~44 KB prelude
   (~0.7–1 s each), so the 20 s budget bailed at ~28 delegations *just after*
   reaching `(= x! y!)` — fragile, and a hair slower would have missed it.

# The fix (26ab129) — two soundness-preserving changes

### 1. Goal-relevance search order (the real fix)
`abduct_goal_relevance` ranks each abducible by
`2·(# goal variables it shares) + 1 if it is a top-level positive equality`,
and the sweep examines the highest score first. For goal `(= (Sub x! y!) 0)`:

| abducible | score |
|---|---|
| `(= x! y!)` | **5** (shares x!,y! + equality) |
| `(> x! y!)`, `(>= x! y!)`, `(not (= x! y!))`, … | 4 |
| `(= x! 0)`, `(= y! 0)` | 3 |
| `(>= x! 0)`, … | 2 |

`(= x! y!)` is now examined **first**, found at the ~3rd delegation instead of
the ~28th — robust against budget/machine slack. This reorders **only** the
search; every candidate still gets the full entailment + consistency check, so
soundness and minimality are untouched.

**Why not a model-guided prune?** That was the first design — get a counterexample
model of `F ∧ ¬G`, keep only abducibles falsified by it. It is *infeasible here*:
over the quantified prelude `F ∧ ¬G` is itself `unknown` (no model), so there is
nothing to prune with. And the cheap-incrementality alternative (assert `F` once,
`push`/assert `H ∧ ¬G`/`check`/`pop` per subset) is **unsound** in vendored OxiZ —
we measured a confirmed *spurious* `unsat` where a popped scope's `(= x! y!)`
leaked into the next check (same family as the SAT-core pop watcher-leak). So the
per-subset check stays a fresh full solve (the complete + sound authority), and
the relevance order is the model-free way to reach the answer in time.

### 2. Batch-first OxiZ delegation
`oxiz_inproc` now tries the whole-buffer `execute_script` (the exact
z3-parity-validated call the corpus harness + file CLI use) before the
per-command fallback — ~0.7 s/subset vs ~0.95 s, widening the margin. Per-command
stays the fallback for inputs batch mis-parses.

### The overflow half (i128) — pending your pointer bump
The other eqvars manifestation (the `assert_eq` `-rhs` overflow on a
single-subset path) is the `external/oxiz` `Rational64 → Ratio<i128>` completion
(`3d72b96`). It is committed in the submodule but the **submodule pointer bump is
yours to land** (we never bump/push it from here).

# Answers to your CCFV A/B findings (the other reply)

- **(ii) native spurious `sat` on `∀x.(p x ∧ ¬p x)` over an un-witnessed sort** —
  **FIXED** (`d6b0d80`). When a bound variable's sort has no ground term, the
  enumerator now instantiates the body at a deterministic fresh constant
  (`!mbqi-fresh!<sort>`), so the `∀x.false` contradiction is exposed → sound
  `unsat`. `∀x.body ⊨ body[fresh]` is a sound consequence (SMT sorts are
  non-empty), so it can only surface an existing unsat, never fabricate one.
  Regression tests `forall_{contradictory,satisfiable}_body_over_empty_universe`
  added.

- **(i) the flip isn't observable through `lu-smt`** — correct, and expected. The
  `:oxiz.ccfv-model-compl` flip changes only OxiZ's `eval_forall` verdict on the
  **model-completion** path. `lu-smt` consults OxiZ only when native returns a
  *plain* `Unknown`; `FX_NEQ_A` lands in native's tier-4 abductive escalation
  instead, so OxiZ's `Sat` is never what `lu-smt` returns for that shape. To
  exercise the flip end-to-end you need a `.smt2` where native returns plain
  `Unknown` (no tier-4) **and** OxiZ's model-completion turns it `Sat` — i.e. a
  trigger-free EUF-disequality `∀` with no abducible vocabulary in scope. Since
  the corpus + your A/B both show **0 recovery**, this stays a curiosity; the flip
  remains opt-in (`false` default) per your Phase 5 verdict. If you want the deeper
  EUF probe, a full vstd `-V adsmt` sweep with `VERUS_ADSMT_PATH` prepending
  `(set-option :oxiz.ccfv-model-compl true)` is the lever — but nothing so far
  contradicts the 0.

# Validation

- Your captured repro: surfaces `(= x! y!)` in ~21 s; control `unknown` ~2.6 s.
- Scoped suites green: `adsmt-cli` (incl. new `abduct_goal_relevance_*` unit
  test), `adsmt-abduce` (32), `adsmt-quant` (43), `adsmt-engine` forall (7).
- Full `cargo test --workspace` + the OxiZ corpus are the user's `!` gates (not
  run here).

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-22
