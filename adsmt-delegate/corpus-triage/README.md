<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# corpus-triage — the #404 tuning-campaign toolkit

Standing tools for the verus-fork per-obligation corpus campaign
(`corpus-2026-07-04-lukb-per-obligation/`, pinned `manifest.tsv`): classify
every `solver-unknown` row against z3, then shrink a chosen render to the
axioms the disagreement actually needs.

- `triage_unknowns.py` — for every pinned `solver-unknown`/`solver-timeout`/
  `stage-bail` row, re-run `adsmtc` (`ADSMT_DELEGATE_DEBUG=1`), capture the
  delegated render, and run z3 on it. `z3=unsat` rows are the REAL
  completeness targets (z3 closes what we abstain on); `z3-noverdict` rows
  are mostly the designed-non-verifying abduct family. Env: `ADSMT_CORPUS`,
  `ADSMTC`. Output: per-row TSV + a `family × (adsmtc, z3)` summary.
- `ddmin_render.py <render.smt2> <out.smt2>` — per-`(assert)` ddmin
  preserving `z3 = unsat ∧ oxiz ≠ unsat` (declarations kept verbatim).
  Env: `OXIZ` (the fork CLI, `cargo build --release -p oxiz-cli` inside
  `external/oxiz`). This is the #396/#397 localization playbook, mechanized.
- `dm3-ob01-ddmin-core.smt2` — the campaign's first localized wall:
  `datatypes-match-3/ob01` shrunk 419 → 5 asserts (the verus
  decreases-check shape: the `check_decrease_height` definition + guarded
  per-field height axioms). z3: `unsat`; the fork engine at `8039884`:
  `unknown`. **CLOSED (fork `b4518db`): now `unsat`, z3 parity.**
- `decreases-check-core.smt2` — the same wall hand-reduced to 14 lines over
  uninterpreted sorts (no datatypes — the shape, not the theory, is the
  discriminator). z3: `unsat`. **CLOSED (fork `3c49a00`): now `unsat`.**

The wall decomposed into FIVE independent engine gaps, isolated by the
probe chain + hand-grounding the MBQI instances (the emitted lemmas were
always fine — the ground core itself was spuriously Sat):

1. frontier-watermark starvation (FIXED, fork `cf878ab`) — a round whose
   e-match step was skipped still aged the frontier, so a freshly-inferred
   trigger never saw the pre-existing ground seeds (`OXIZ_MBQI_DBG=1`
   showed `ematch_all -> 0` flipping to 8);
2. SAT-layer inert incremental clauses (FIXED, fork `3c49a00`) — a clause
   added post-solve whose false literals were assigned BEFORE insertion
   was never visited by propagation again, so the instance lemma's guard
   Tseitin never forced its `and` node (`propagate_added_unit` + the
   front-position watch-selection invariant);
3. tester-shape diseqs invisible to `check_dt` (FIXED, fork `b4518db`) —
   `v ≠ C(sel_{C,0}(v), …)` IS `¬is-C(v)` for any arity (the verus
   decreases-check guard form), now recognized positionally in BOTH
   selector representations (`DtSelector` node / plain `Apply`);
4. no ground exhaustiveness under search (FIXED, fork `b4518db`) —
   constructor COVER (`≥1` shape) + pairwise EXCLUSION (`≤1` shape)
   axioms per datatype-sorted subterm, hash-cons-identical to the goal's
   own guard atoms, so the "no shape at all" / "two shapes at once"
   escapes die propositionally;
5. datatype nodes opaque to EUF congruence (FIXED, fork `b4518db`) —
   `DtConstructor`/`DtSelector` now intern as function applications, so
   `init = E` bridges shape atoms across equal terms in-search.

Gates run for the batch: fork suites green (oxiz-core/sat/mbqi 1944/0,
oxiz-solver 834/0 incl. the new `dt_ground_completeness_regression.rs`),
`dt_render_differential.py` 3000 seeds 0-spurious, a new ground-DT
SMT-LIB differential (`dt_smt_diff.py`, jobs tmp) 2000 seeds
SPURIOUS_UNSAT=0, full-corpus re-sweep vs the pinned manifest. The same
SMT-LIB differential measured a PRE-EXISTING sat-side completeness wall
(selector-of-ctor reduction on the Apply form / acyclicity / injectivity,
352/2000 spurious-sat) — tracked as task #406.

Full-corpus re-sweep vs the pinned manifest: 33 stage-bail conversions
(#403's elaboration — 20 verified / 12 solver-unknown / 1 timeout),
**20 solver-unknown → verified** (fuel-recursion ×7, seq-vstd ×6,
divmod-real ×3, datatypes-match-1 ×1, linear-euf ×2, nonlinear ×1),
negative controls 4/4 (`neg-exhaustiveness-control` STAYS `sat` — the
cover axioms do not over-constrain). CANONICAL LEDGER (reconciled
row-by-row with verus-fork's independent 90s re-sweep at `b4518db`):
**143 verified** (104 pinned + 40 − 1), remaining z3-unsat targets
**53**. Two sweep-hygiene lessons from the reconciliation: (a) summary
counts in replies/docs are computed by SCRIPT from the sweep log, never
tallied by hand (two prose-tally slips in two replies); (b) a sweep
whose engine has a WALL-CLOCK guard (the 3s MBQI non-termination guard)
must run on an otherwise-idle machine — running it alongside test
suites/differentials pushed two ~740ms rows past the guard and
misclassified them solver-unknown. Honest residuals: (a)
`fuel-recursion-1/ob06` regressed verified → solver-unknown — bisected to
the (mandatory) gap-2 SAT fix `3c49a00`: the now-biting lemmas change the
per-round model and the `sum_to` recursion axiom enters a term-growth
spiral (`nClip(Sub(%I(I(nClip(…)))))` self-feeding instances) that
previously happened to converge; the row rejoins the z3-unsat target
list. (b) the FULL dm3/ob01 render (419 asserts) is still solver-unknown
(~5s, self-terminating — NOT a budget cut: `-t 60` changes nothing) even
though its ddmin core closed; the residual is instantiation-side over
the full axiom set. Both are the campaign's continuing tuning surface
(term-growth throttle / relevance-gate), not ground-theory gaps.

**Update 2026-07-13 (verus-fork resweep @ oxiz `b478199`, ground-DT
completeness rounds #406/#418/#419/#422/#423/#424 — selector-reduction,
acyclicity, well-foundedness, injectivity via a shared equality-closure
fixpoint, `distinct` polarity, OR-branch case-splitting, cross-datatype
name collisions, N-ary `distinct`, literal-constant conflicts):
**CANONICAL LEDGER 145 verified / 50 remaining z3-unsat targets** (+2 vs
the 143/53 above). Residual (b) above (`dm3/ob01`'s full 419-assert
render) is now **CLOSED** — verified in 1.14s; `dm3/ob03` also newly
verified (1.46s). Zero new regressions (`ob06` unchanged, still the sole
one), negative controls 4/4 exact (the new acyclicity/injectivity/
cover/`distinct`-decomposition machinery does not over-constrain).
"verus exposure" reconfirmed nil across the full #406-#424 span, not
just #406. Saturator bench list (10 rows, current-pin) delivered:
`.local-replies-from/verus-fork/corpus-saturators-2026-07-13-b478199.txt`
— to be used as the first regression-pin once the fuel-throttle/
relevance-gate slice (residual (a) above) lands.

Verdict-trust rule: any change motivated by these tools that can produce a
NEW `unsat` goes through the fork suites + a full-corpus re-sweep against
the pinned manifest (0 regressions, negative controls exact) before it
lands — see `feedback_z3_differential_for_unsat_trust`.
