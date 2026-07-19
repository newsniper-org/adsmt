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

**Update 2026-07-17 (adsmt-side: lukb `trigger` → OxiZ `:pattern`
threading — the dm2-class root fix)**: the delegated renders carried ZERO
`:pattern` (the elaborator dropped the surface `trigger` clauses at its
documented TODO), so OxiZ's own trigger inference picked guard-shaped
(`has_type`) and 2-variable triggers → 3–4 orders of magnitude
over-instantiation vs z3 (dm2/ob01: 2.3M matches, 100% unevaluable
lemmas). Now threaded end-to-end, out-of-band at every stage: elaborator
side-map keyed by the hash-consed outermost Π (patterns elaborated in the
body's binder window; any failure drops only that quantifier's triggers —
advisory metadata never rejects a module) → lower multi-binder takeover
(`peel_pis` by recorded arity, body+patterns in one frame, byte-identical
fold to the plain path, re-keyed through `fold_bool_lits`) → render binder
re-collection + `(! body :pattern …)` emission behind an all-or-nothing
dead-pattern guard (renderable ∧ per-group full binder cover ∧ head
uninterpreted, saturated, and FREE-occurring in the body ∧ pattern decls
collected). Completeness is floored DYNAMICALLY (`proves_goal`): if the
annotated script doesn't prove, the obligation re-runs in the historical
curried pattern-free shape — every pre-feature `unsat` stays `unsat` by
construction (the adversarial gate caught seq-vstd-1/ob08+ob09 flipping
verified→unknown from legitimate-but-engine-hostile patterns; the floor
restored both). `ADSMT_DELEGATE_NO_PATTERNS=1` is the A/B kill-switch.
Full-corpus gate: **LOCAL LEDGER 153 verified** (+5 over the 148
guard-scope-campaign baseline: `datatypes-match-2/ob01` — the dm2
headline, unknown-at-any-guard → 765 ms; `datatypes-match-2/ob07` — the
former stack-overflow row; `datatypes-match-2/ob08`;
`fuel-recursion-2/ob07`; `seq-vstd-2/ob04`), **zero verified→unknown
flips**, `ob06` unchanged sole pinned regression, saturators 0, negative
controls 4/4 exact. `seq-vstd-2/ob01` (sv2) remains speed-bound (42.9 s
e2e at a 90 s guard — the sweep-protocol proposal), not trigger-bound.
NEW upstream issue **#425** (engine-side, out of scope here): a dead or
ill-arity EXPLICIT pattern makes standalone OxiZ answer a spurious `sat`
on an unsat problem — explicit patterns suppress inference with zero
validation and MBQI never model-checks trigger-guided quantifiers
(repros: `425-dead-pattern-spurious-sat.smt2`,
`425-illarity-pattern-spurious-sat.smt2` in this directory; z3 `unsat`
both). adsmt is doubly shielded (never-trust-`sat` delegation posture +
the completeness floor), so within adsmt the failure class is
verdict-denial only — and the render guards drop exactly those pattern
shapes.

**Update 2026-07-18 (sweep-protocol v2 ADOPTED — verus-fork accepted the
`OXIZ_MBQI_GUARD_MS=90000` proposal)**: both sides' harnesses now pin the
engine guard to the 90 s per-row wall (`resweep.py` in this directory is
the promoted standing harness — guard as argv[1], `default` for the old
4 s behavior; idle-machine-only unchanged). verus-fork's transition
DUAL sweep @ AD1 `de78325` / oxiz `0c75ad7`: default-guard **153**
(exactly matches our local — all +5 reproduced, dm2/ob01 769 ms);
90 s-guard (v2) **CANONICAL LEDGER 155 verified / 21 unknown-or-bail /
29 saturators / negatives 4/4 exact even at 22× budget**. The two v2
gains: `seq-vstd-2/ob01` (sv2) **21.4 s unsat** — the speed-bound row the
protocol was proposed for (half of the pre-perf 42.9 s measurement: the
`37bad45`/`f7c3cce`/`0c75ad7` trio's dividend) — and the HEADLINE:
`fuel-recursion-1/ob06`, the campaign's sole regression (gap-2-induced
term-growth spiral), **converges to `unsat` within the 90 s budget** —
the regression ledger is 0 for the first time, and the spiral is
evidence of SLOW CONVERGENCE, not divergence (further deprioritizes the
already-net-negative term-growth throttle). Both v2 claims re-verified
first-hand here: ob06 8.5 s, sv2/ob01 21.7 s. The 29 v2 saturators
(named in the 2026-07-18 inbox message) are the refreshed
throttle-bench list — the expected v2 cost (rows that used to
self-abandon at 4 s now burn full budget; sweep ~44 min idle). Formal
re-pin CONFIRMED 2026-07-18 at the pushed pins (AD1 `671937f` / oxiz
`0c75ad7`): 155/21/29, regression 0, negatives 4/4 — ROW-IDENTICAL to
the dual sweep (all 51 CONV + 29 SATURATOR rows match; wall-ms jitter
only). 155/21/29 is the mutually-pinned canonical ledger; next re-pin
trigger = the next landed engine/completeness slice.

**Update 2026-07-19 (engine campaign slice E1, oxiz `d39bd09` — #425
closed; LOCAL LEDGER 158)**: the #425 spurious-sat class (dead/ill-arity
explicit `:pattern` suppressing both inference and model verification) is
closed default-ON: provably-unmatchable-only static gate + ever-fired
tracking + the new `SaturatedUnverified` confirm-but-never-sat verdict
(restores the old exemption's beneficial early-stop soundly — without it
dm3-class rows flooded anti-monotonically with the guard). v2 gate:
**158 verified / 27 saturators / 20 unknown-or-bail / negatives 4/4 /
zero canonical flips** (+3: `fuel-recursion-2/ob13` + `seq-vstd-2/ob09`
— former 90 s saturators — and `linear-euf-1/ob05`). Randomized pattern
differential (z3-ref + cvc5): 3000 total seeds, gated spurious 0 both
modes. Additive-patterns mode ships DEFAULT OFF (`OXIZ_MBQI_ADDITIVE=1`
opt-in): its A/B also reaches 158 but trades sideways — loses 3
canonical rows (dm3/ob01, fr2/ob03, fr3/ob16) for 5 other saturators
(dm3/ob05, fr3/ob12, sv1/ob03, sv1/ob06, sv3/ob08) at ~+80% wall on
budget-bound rows; the union (163) marks a per-row additive-retry policy
as a follow-up lever. NEW ledger items: **#426** fired-but-insufficient
parsed-trigger exemption = standalone spurious-sat class (31/2000 seeds,
zeroed by additive, adsmt shielded by never-trust-sat); **#427**
`(set-logic ALL)` Saturated-confirm misses EUF↔LIA cross-theory
conflicts (pre-existing, UFLIA correct); **Dt-as-App view upgrade**
(constructor/selector applications currently view Opaque — real Dt-headed
trigger matchability, the recovery lever for dm2/ob03) — all three are
future engine slices.

**Update 2026-07-19 (engine campaign slice S, oxiz `4a8b29d` — simplex
trail infrastructure, opt-in)**: clone-on-push replaced by a single-funnel
undo trail as `BacktrackMode::Trail` (`OXIZ_SIMPLEX_TRAIL=1`), measured
push+pop containment 46.1%→0.01%, RSS −39%, recording overhead
unmeasurable, 12,800-op committed + 204,800-op adversarial differential
zero-divergence. **Snapshot stays DEFAULT** (kill criterion fired): the
freed throughput is reinvested by guard-bound MBQI rows — the Trail A/B
closed 2 simplex-bound saturators (seq-vstd-2/ob03, datatypes-match-3/
ob05) but drowned 5 fuel-recursion rows (3 canonical). Pivot-victim
selection is mode-split (Snapshot = legacy map-order, byte-identical
trunk trajectory; Trail = Bland smallest-VarId, layout-independent).
Final gate: **158 / 27 / 20 ROW-IDENTICAL to E1**, negatives 4/4.
Follow-up gate for Trail-default: work-bounded (not deadline-bounded)
round emission. New pre-existing leads ledgered: Bland 10k-pivot-cap
cycling → incomplete; `dual_simplex` cap path missing `incomplete`
(spurious-sat-shaped, no callers); `propagate_bounds`/`tighten_bounds`
trail-free bound writes (survive pop, API in-tree-dead).

Verdict-trust rule: any change motivated by these tools that can produce a
NEW `unsat` goes through the fork suites + a full-corpus re-sweep against
the pinned manifest (0 regressions, negative controls exact) before it
lands — see `feedback_z3_differential_for_unsat_trust`.
