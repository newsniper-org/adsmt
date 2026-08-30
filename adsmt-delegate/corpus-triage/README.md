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
(Since 2026-08-02 the ladder has a THIRD rung between those two — the
pattern-free render in the annotated script's RE-COLLECTED binder shape,
budget-capped at a sixth of the guard; see the Lead-2 update below.)
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

**Update 2026-07-19 (engine campaign slice E2a, oxiz `dd2714f` — hop
instrumentation landed, E2b KILLED by measurement)**: feature
`euf-find-stats` (byte-identical at rest) measured avg hops/find **< 1 on
every row** (the EUF-bound saturator fr2/ob09 flattest at 0.517 across
6.99e9 finds, 100M finds/s) — union-by-rank already keeps the forest
flat, so trailed path compression (E2b) is killed before implementation;
EufSolver::propagate dominance is call-VOLUME-driven. Recorded lever for
the EUF-bound class: fewer find calls / cheaper per-call constant /
canonical-args caching. Campaign slice status: E1 ✓ / S ✓ (infra,
Snapshot default) / E2a ✓ / E2b killed / R deferred (gate met only on
sv2/ob03). **verus-fork re-pin CONFIRMED 2026-07-20 @ oxiz `dd2714f`:
v2 sweep 158 / 20 / 27 / regressions 0 / negatives 4/4 — exact, +3
conversions row-identical (fuel-recursion-2/ob13, linear-euf-1/ob05,
seq-vstd-2/ob09), saturators 29→27 explained row-for-row (fr2/ob13 +
sv2/ob09 in-guard-converted via the SaturatedUnverified confirm).
158/20/27 is the mutually-pinned canonical ledger.**

**Update 2026-07-20/21 (MaxSAT integration, branch
`0.2.4-fill-the-gap/maxsat` forked from `0.2.4-redesign` @ `dd2714f`) —
P0 + P1 landed, not yet merged:**

- **P0 (`ce47dbe`)**: fixed 3 pre-existing wrong-answer bugs — pmres.rs +
  pmres_enhanced.rs relax-var aliasing (upfront global next_var seeding,
  applied independently to both non-sharing implementations), sortmax.rs
  + cardinality_network.rs sorting-network output-orientation (the
  ascending network's easy/hard-threshold ends were swapped; a latent
  twin in cardinality_network's own at-most-k Sorting branch was fixed
  alongside it, previously untested for semantic correctness). 4
  additional latent bugs found via differential and fixed in the same
  pass. **rc2.rs itself was found unsound** during differential
  (stratified path reported cost 3 on a brute-force-verified optimum of
  7) — the differential's oracle was switched to brute-force enumeration
  instead. `rc2_enhanced.rs` is an independently-coded duplicate (same
  non-sharing pattern as pmres/pmres_enhanced) so does not mechanically
  inherit rc2.rs's bug, but is **unverified** — anything depending on its
  stratification (P2's ASP weak-constraint design explicitly does) must
  run its own differential first. oxiz-opt ignored-failures 3→0;
  project-wide tolerated ignored-failure ledger 5→2 (only oxiz-nl2
  `differential_full` + oxiz-spacer `test_counter_unsafe` remain).
- **P1 (fixup landed on top of the implementer's initial pass, same
  branch, not yet committed as of this note)**: wired
  `(maximize)/(minimize)/(assert-soft)/(get-objectives)` end-to-end via
  a new `oxiz_core::ast::manager::transplant_term` (iterative, memoized,
  DAG-sharing-preserving; builtin sorts Bool/Int/Real only — non-builtin
  sorts fail cleanly) bridging `oxiz_solver::Context`'s TermManager to
  `oxiz_opt::OptContext`'s own (a genuine cyclic-dependency constraint
  ruled out embedding `OptContext` directly in `oxiz-solver`; the
  integration lives in new `oxiz-opt/src/script.rs::OptScriptRunner`
  instead). The initial MaxSAT-cost binary-search path
  (`OptContext::optimize_maxsmt`) was replaced for the pure-Boolean
  fragment by a new `oxiz-opt/src/bool_cnf_maxsat.rs` (Tseitin CNF +
  totalizer-based binary search over the raw `oxiz_sat::Solver`) after
  the original LIA-selector encoding was shown to be **unreliable at
  6+ selector groups** — repro below. `PmresSolver` was tried first per
  plan but found **weight-blind on mixed-weight multi-literal cores**
  (reports cost 20 where the true optimum is 5) and abandoned for this
  purpose. z3 optimum-correctness differential (the primary gate, exact
  value not just SAT/UNSAT): **300/300 = 100%** on the maxsat + omt_bare
  categories (5 independent re-runs during fixup, reconfirmed by the
  main session with a fresh seed). Two categories explicitly NOT counted
  in the gate, both pre-existing/orthogonal: `omt_compound`
  (`optimize_single_objective`'s unbounded-detection reports `∞` for any
  non-bare-variable objective, even trivially-bounded ones — pre-existing
  `OptContext` gap, untouched by this slice) and `maxsat_grouped` (`:id`
  soft-constraint group-reporting semantics diverge from z3's convention
  — open design question, not a known-wrong bug, tracked separately).
  Corpus spot-check: 168-row z3-parity suite unchanged (165 agree / 2
  sound-incomplete / 1 stronger-than-z3 / 0 spurious); 5 representative
  adsmtc corpus rows re-verified unsat with unchanged verdicts (no
  corpus row uses optimization commands — the no-objective `CheckSat`
  path is structurally byte-identical to pre-P1, confirmed by git-stash
  diffing 10 non-optimization scripts pre/post).

**NEW upstream issue #428 (oxiz core engine, independent of MaxSAT,
found via P1's adversarial lens + confirmed by the main session)**: the
BASE `oxiz_solver::Solver` (zero MaxSAT/opt code involved) returns a
**false UNSAT on QF_LIA** for a specific Bool-selector + integer-cost-sum
encoding shape once the formula reaches **6 independent selector/cost
groups** summed into one linear inequality (5 groups: correct `sat`; 6
groups: `unsat`) — z3 AND cvc5 both independently confirm `sat` with a
matching witness on the same script. Minimized repro (36 lines, 6
selector groups, no `get-model` needed to reproduce) preserved at
`428-qflia-false-unsat-6plus-selector-groups.smt2`; the original
41-line/`optimize_maxsmt`-shaped repro at
`428-qflia-false-unsat-original-repro.smt2`. This is the genuine root
cause `optimize_maxsmt`'s binary-search MaxSAT path inherited (not
merely "a suboptimal search heuristic" as first characterized) — the
`bool_cnf_maxsat.rs` fast-path sidesteps it for pure-Boolean MaxSAT by
never emitting Int cost variables, but the general LIA-mixed fallback
path (still reachable for problems with non-Boolean hard constraints)
remains exposed. Scope: this is a base-engine soundness-class bug
(false UNSAT), NOT specific to MaxSAT — any QF_LIA consumer hitting this
selector-group shape is at risk; flagging as the highest-priority
follow-up independent of the MaxSAT initiative's own P2/P3.

**P2 (AD1 `4913cf6`) — ASP weak constraints, single-level, adsmt-side
only (external/oxiz untouched)**: `:~ body. [weight@0]` surface syntax
in adsmt-ir-asp (lexer/parser/AST/elaborator, integer-only weights, 2+
distinct levels cleanly rejected per the L3 first-slice-only precedent).
Two semantics resolved empirically against real clingo 5.8.0 rather than
guessed: polarity (pays weight when body HOLDS) and — the deeper,
genuinely non-obvious subtlety — **counting**: ASP-Core-2 identifies a
ground instance by `(weight, level, terms)`; with no `terms` clause in
this grammar, clingo collapses every satisfied ground instance sharing
an identical `(weight, level)` into ONE counted unit **globally across
the whole program** (`p(1..3). :~ p(X). [5@0]` costs 5, not 15; three
separate declarations sharing weight 5 also collapse to 5) — verified 3
independent ways before implementing, re-verified independently by the
adversarial lens with a from-scratch generator (400 more seeded cases,
0 mismatches) plus hand-derived adversarial cases (dead bodies,
negative/reward weights, negated-body constraints, duplicate
declarations, theory-guarded bodies). Search scope: reuses the existing
GL-reduct-verified stable-model enumeration unchanged and picks the
cost-minimal candidate by plain evaluation (argmin over already-decided
models) rather than a new weight-aware decision procedure — the
pre-authorized simpler-but-correct alternative. Delegate boundary
(`adsmt-delegate/src/asp.rs`) deliberately does NOT invoke an
oxiz_sat/MaxSAT search (nothing left to search once a candidate model is
fixed — only a cost to sum); cost still renders through
`oxiz_opt::maxsat::Weight::Int` for downstream consistency.

Adversarial pass caught a real P0: `weak_cost` summed satisfied weights
as unchecked `i64` — the workspace's actual release profile (no
overflow-checks) silently wrapped and sign-flipped the optimal cost on
overflow, no error (debug hard-panicked instead). Fixed: sum in `i128`,
check the total fits `i64`, abstain (`FaceError::Unsupported`) on
overflow rather than report a wrapped number — reproduced through the
real release binary before/after the fix.

Gate: clingo optimal-cost differential (soundness-class, same discipline
as P0/P1's z3 differential), 150 seeded programs, **150/150 exact
match**; adversarial lens independently re-ran 400 more, 0 mismatches.
Suites: adsmt-ir-asp 182/0, adsmt-delegate `--features asp` 17/0.

**P3 (AD1 `5d337f8`) — weighted abduction / MPE, adsmt-side only,
COMPLETES the P0-P3 initiative**: optional `:weight w` cost on
`(declare-abducible ...)` (default 1.0, byte-identical backward-compat
with every existing unweighted script — verified structurally and
empirically). Two design questions resolved by following P2's own
just-set precedent for the identical structural shape: **scope** =
re-rank an already-enumerated, already-minimality-pruned candidate set
(argmin over a short list), not a fresh weighted-MPE search replacing
the SLD/subset enumeration; **no live oxiz-opt/MaxSAT solver call** —
wrapping an already-decided argmin in a fresh search adds a new
untrusted surface for zero benefit, the exact reasoning P2's
`adsmt-delegate/src/asp.rs` module doc gives, cited explicitly. Zero new
Cargo deps; `external/oxiz` untouched. Consolidates the two previously-
independent scoring paths (`adsmt-abduce::rank_candidates`'s
cardinality+depth score and `adsmt-cli`'s separate
`abduct_goal_relevance`-ordered subset-size score inside
`abduce_theory`) through one `candidate_cost = Σweight(h) + 0.001*depth`.

Gate: brute-force optimal-ranking differential (soundness-class — a
worse-than-available candidate ranked #1 is the same bug class as
P0/P1/P2's wrong-optimum findings), 150 seeded instances +
adversarial-lens independent 500-instance re-run (600 combined, 0
beaten), mutation-tested (reversed comparator caught at iteration 0).
`f64` weight arithmetic saturates to `+Infinity` on overflow rather than
wrapping — explicitly confirmed to NOT reproduce P2's `i64`-wrap bug
class via the identical sum-of-weights pattern. Adversarial pass caught
one real P1 (malformed `:weight` silently defaulted to 1.0 instead of
erroring — fixed, hard-errors now). Known documented boundary (not a
bug): `:weight 0` (the standard "free hypothesis" MPE case) is rejected
at the CLI validation layer even though the ranking engine itself
handles it correctly — a conservative choice, not silently loosened.
Suites: adsmt-abduce 36/0 + differential 2/0, adsmt-parser-smtlib2
60/0, adsmt-engine 210/0, adsmt-cli 37/0 (+39/0 with oxiz feature).

**MaxSAT P0-P3 initiative COMPLETE.** oxiz-opt went from a 16.6k-LoC
unwired liability (3 wrong-answer ignored-test failures) to a sound,
wired, differential-verified asset backing two previously-design-only
adsmt features (ASP weak constraints, weighted abduction). One new
top-priority independent lead surfaced along the way: **#428** (base
`oxiz_solver::Solver` QF_LIA false-UNSAT at 6+ selector/cost groups,
scope-note above) — resuming the verus-facing engine-perf follow-up
pool per [[engine_algorithmics_campaign]] is next, with #428 as the
new highest-priority item in that pool.

**Update 2026-07-21 (oxiz `b191c71`) — #428 CLOSED, plus a second,
more-severe soundness bug found and closed in the same pass:**

- **#428 root cause**: `check_subsumption` (oxiz-sat/src/solver/learn.rs)
  was the one clause-removal call site in that module never scrubbed for
  stale watchers before recycling a clause id — the **4th recurrence**
  of the clause-id-recycle stale-watcher bug class this project has now
  fixed (see `feedback_pop_scrub_cache_bug_class`), independently in
  three sibling call sites each time before. A stale watcher silently
  attaches to an unrelated recycled clause, mis-propagates a bogus unit
  fact, and 1-UIP conflict analysis pins it permanently — false UNSAT.
  Fixed with the same +27-line scrub pattern the three siblings already
  carry.
- **NEW bug found by #428's own adversarial verification, MORE severe
  (false-SAT, not false-UNSAT)**: a linear-arithmetic equality reachable
  at negative polarity via the antecedent of `Implies`, the condition of
  `Ite`, or a bare `Or` disjunct was never told to the arithmetic
  (simplex) solver as a disequality — the old syntactic AST pre-pass
  covering this only pattern-matched a hand-picked subset of shapes.
  **88.4% reproduction rate** (221/250 seeds) on cancellation-form
  equalities (e.g. `(= (+ X1 X0) (+ X2 X0))`). Fixed at the mechanism
  level: an unconditional sound trichotomy clause
  `Eq(lhs,rhs) ∨ Lt(lhs,rhs) ∨ Gt(lhs,rhs)` at the single Tseitin
  encode choke-point for every Int/Real equality atom, closing every
  syntactic position at once (not enumerating more AST shapes).
- **Verification** (both are soundness-class, gated at this project's
  highest rigor): #428-shape z3 differential 1500/1500 seeds 0
  mismatches (harness pre-validated against a genuine pre-fix binary);
  broad general-QF_LIA z3 differential 900+1500 seeds combined, 0
  mismatches post-fix (was 88.4% false-sat pre-fix on the trichotomy
  gap); threshold/stress sweep 231 trials 0 mismatches; workspace suite
  7381/0.
- **Corpus impact (full 209-row v2 gate, run by the main session — NOT
  just the fixup's 50-row sample, which only caught 1 of the 3 actual
  losses)**: **159 verified** (was 158), **0 regressions vs the PINNED
  manifest**, negatives 4/4. Real row-level churn disclosed in full:
  +4 (fuel-recursion-2/ob05, fuel-recursion-3/ob07/ob10/ob12;
  fuel-recursion-2/ob07 — the fixup's one caught case — recovers
  cleanly at the v2 90s guard) vs **3 losses that do NOT recover even
  at a 300s guard** (checked by hand): `datatypes-match-3/ob03` (fast
  unknown ~3.1s, guard-independent), `fuel-recursion-3/ob14`
  (self-terminating unknown ~65s), `fuel-recursion-2/ob13` (genuine
  saturator, still times out at 300s). All three losses are **sound**
  (unknown/timeout, never a wrong answer) and mechanistically consistent
  with the fix's own documented cost (new ground `Lt`/`Gt` atoms feed
  MBQI's trigger-matching corpus, perturbing instantiation search on
  quantifier-heavy rows — one row measured 510→2206 instantiations).
  **This fix is mandatory, not opt-in-able** (unlike the S slice's Trail
  mode): there is no sound way to toggle off a confirmed false-UNSAT and
  an 88%-reproducible false-SAT, so it lands despite the churn.
- **159/21/25** (verified/unknown-or-bail/saturator) is the new local
  ledger pending verus-fork re-pin.

Verdict-trust rule: any change motivated by these tools that can produce a
NEW `unsat` goes through the fork suites + a full-corpus re-sweep against
the pinned manifest (0 regressions, negative controls exact) before it
lands — see `feedback_z3_differential_for_unsat_trust`.

**Update 2026-08-02 — #427 CLOSED (root cause was NOT the recorded
framing), and it turns out the whole lukb corpus had been running with
integer arithmetic relaxed to rationals:**

- **Real root cause** (the old "`(set-logic ALL)`'s Saturated confirm
  misses EUF↔LIA cross-theory conflicts" framing was wrong):
  `ArithSolver` carried ONE GLOBAL `is_integer` flag, chosen by
  **substring-matching the `(set-logic …)` name** (`NIA`/`NRA`/`LIA`/
  `IDL`/`LRA`/`RDL`/`BV`) and defaulting to LRA when nothing matched.
  So `(set-logic ALL)`, **no `(set-logic)` at all**, and `AUFLIRA` all
  ran Int problems through the *rational* solver. Every integrality
  mechanism was gated on that one flag: the integer branch-and-bound in
  `Theory::check`, `assert_lt`/`assert_gt`'s `x<k ⇒ x≤k−1`
  strengthening, `assert_eq`'s GCD-infeasibility test, `value()`,
  `fixed_value_with_reasons`. Minimized from the reported quantified
  pigeonhole down to **four lines with no quantifier, no UF, no counting
  argument**: `(set-logic ALL)(declare-const x Int)(assert (> x 0))
  (assert (< x 1))` → z3 `unsat`, oxiz `sat`. Repros:
  `427-set-logic-all-int-as-rational-{minimal,pigeonhole}.smt2`.
- **Fix**: per-term integrality — `declared_sorts: FxHashMap<TermId,bool>`
  in `ArithSolver`, every gate above re-keyed to the *term's sort*, with
  the old global flag kept as fallback for undeclared terms (so
  correctly-logic-named paths stay bit-identical). Sorts are declared at
  the 4 arith-intern sites in `encode.rs` and 3 assertion sites in
  `theory_manager.rs`. `config.rs` deliberately UNCHANGED: the obvious
  `ALL → lia()` mapping is a **proven-wrong** fix — it creates a mirror
  **false-UNSAT** on `(set-logic ALL)(declare-const r Real)(assert
  (> r 0.0))(assert (< r 1.0))`, verified experimentally before being
  rejected. Three further unsound edges closed as a consequence: a
  `Real` under any `…LIA…`-named logic was being forced integral
  (false-UNSAT); `assert_lt` over-tightened on fractional rhs
  (`2x < 1/2` → `2x ≤ −1/2`, excluding `x = 0`); GCD-infeasibility fired
  on fractional coefficients.
- **THE COROLLARY THAT MATTERS FOR THIS CORPUS**: `adsmt-delegate`'s
  `TheoryFlags::logic()` (lib.rs) emits **`ALL` for everything** except
  quantifier-free nonlinear obligations. So *every* Int-arithmetic
  obligation in the 209-row corpus has been solved with a rational
  relaxation for this entire campaign. This never produced a wrong
  `verified` — a rational relaxation makes formulas *more* satisfiable,
  so it can only cause failure-to-prove, and adsmt trusts `unsat` only —
  but it means every prior corpus number was measured with integer
  reasoning effectively switched off. The fix turns it on for the first
  time (`fuel-recursion-1/ob10`: a 90 s full-budget saturator → **`unsat`
  in 4 s**).
- **Verification** (soundness-class rigor, as #428): implementer
  differentials 660 + 560 + 400 seeds; an INDEPENDENT adversarial lens
  wrote its own generator from scratch and ran **1800 randomized seeds +
  ~70 hand-built cases under a dual z3∧cvc5 oracle — 0 mismatches in
  either direction** on the fixed binary (pre-fix, same harness: **239
  false-SATs**, so the harness is proven non-vacuous). Workspace suite
  **7404 passed / 0 failed**; `--ignored` tolerated set exactly the
  usual 2. The lens also cleared all five self-flagged risk items with
  evidence — notably that `declared_sorts` not being rolled back on
  `pop` is **structurally safe**: `TermId`s come from a monotone
  counter over an append-only arena (no `truncate`/`pop`/`clear`
  anywhere), and vars are hash-consed by `(name, sort)`, so `v:Int` and
  `v:Real` are distinct ids.
- **Corpus gate (v2, full 209 rows, main session)**: **158 verified /
  19 unknown-or-bail / 28 saturators**, 0 regressions vs the PINNED
  manifest, **negative controls 8/8** (including verus-fork's four new
  trichotomy controls). Net **−1 vs the 159 canonical**, accounted
  row-by-row: **+1** `fuel-recursion-1/ob10` (saturator → verified,
  4 s); **−1** `fuel-recursion-3/ob07` — **not a capability loss**: it
  still proves `unsat` at the 90 s guard, but its wall grew 88.5 s →
  168 s and the harness's 90 s per-row subprocess cutoff now cuts it
  (this is *exactly* the row verus-fork's Lead 3 flagged as a 1.5 s
  margin that "could flip on machine load"); **−1** `seq-vstd-3/ob06` —
  a genuine completeness loss (self-terminating `unknown` at 170 s
  wall). Two further rows moved unknown-or-bail → saturator (both
  already non-verified, so no verified loss). All losses are sound
  (`unknown`/timeout, never a wrong answer). Cause is the known perf
  cost: `ALL`-logic Int problems now take the correct-but-slower LIA
  branch-and-bound path — the adversarial lens confirmed this is **not a
  new algorithmic regression** (the same rows rewritten with a `QF_LIA`
  header are identically slow on the *pre-fix* binary; the fix merely
  makes `ALL` reach that path).
- **Mandatory, not opt-in-able** — same reasoning as #428: there is no
  sound way to keep shipping a solver that answers `sat` for
  `0 < x < 1` over an `Int`.

**NEW issue #429 — Int-sorted terms produced by OTHER theories never
reach arithmetic integrality at all** (found by #427's adversarial lens,
**orthogonal to #427**: all four reproduce under LIA-named logics where
the global flag was already correct, so no sort-declaration gap can
explain them). Each returns `sat` where **z3 and cvc5 both** say `unsat`,
confirmed first-hand: a quantified UF application with no ground trigger
(`(forall ((i Int)) (and (> (f i) 0) (< (f i) 1)))` under `AUFLIA`), a
datatype selector (`0 < (fst p) < 1`), `str.len`, and `bv2nat`. Repros:
`429-int-from-other-theory-{quantified-uf,dt-selector,strlen,bv2nat}.smt2`.
Control proving the header really selects integer mode: a plain
`(declare-const x Int) 0<x<1` under the same header is correctly `unsat`
even pre-fix.

**Update 2026-08-02 — #429 CLOSED (partially) + a class-level invariant
that found a 5th live instance of the clause-recycle bug; ledger back to
159:**

- **#429** (oxiz `9dec53c`) turned out to be **three distinct mechanisms**
  plus one unimplemented operator, not one bug. (i) `extract_linear_terms`
  whitelists the kinds it can decompose and returns `None` otherwise; that
  `None` propagates out of `parse_arith_comparison` so **nothing at all**
  is asserted into the simplex — the comparison survives only as a free
  Boolean the SAT layer satisfies by fiat, which is why `0 < (fst p) < 1`
  was `sat` (BOTH atoms vanished). Fixed with a two-pass parse: the strict
  pass is unchanged (existing formulas bit-identical), a relaxed retry
  admits an undecomposable subterm as ONE opaque Nelson-Oppen interface
  variable. (ii) The interface variable carried no domain axiom —
  `str.len ≥ 0` was never told to arithmetic, a separate false-SAT that
  only surfaced once (i) was fixed. (iii) MBQI's constant-range completion
  tested interval emptiness over the **rationals**, so `∀i. 0 < f(i) < 1`
  for `f : Int → Int` certified a saturation that does not exist.
  `bv2nat` is not implemented at all (no parser builtin) — added to the
  undecided-op list so it abstains soundly rather than guessing; a real
  BV↔Int bridge is deferred. Result: 2 of the 4 repros now `unsat`, 2
  downgraded from false-`sat` to sound `unknown` (honest partial close —
  the quantified-UF row has no ground terms so e-matching yields zero
  bindings). Differential: 657 checked, 0 mismatches either direction;
  **same seeds pre-fix: 197 false-SAT (29.9%)**.
- **Class-level invariant** (oxiz `ad42391`), answering verus-fork's Q2
  ("the base rate predicts a 5th recurrence"): `ClauseDatabase::remove`
  now *requires* the watcher sink as an argument (`remove(id, &mut impl
  ClauseIndexScrub)`), so removing without scrubbing is **not
  expressible** — pinned by a permanent `compile_fail` doctest — plus two
  O(1) `debug_assert`s at the consumption points as a backstop for the
  one escape hatch Rust's visibility rules leave nameable. Rejected
  alternatives are recorded with their costs (generation-tagged
  `ClauseId`: +50% on `Watcher`, the solver's hottest structure, and it
  *tolerates* leaks rather than preventing them; no-recycling: ≥64 B
  leaked per deleted slot forever).
  **It found the 5th instance the day it was installed**: `vivify_clauses`
  is live and ungated (every 10th restart after a DB reduction) and
  removed a literal in place with no watch repair — when the dropped index
  was 0 or 1 it deleted a *watched* literal, so `propagate` could skip a
  clause that is actually unit. "Would have caught the 4 known
  recurrences" was **measured, not asserted**: reverting each historical
  fix and running that bug's own regression gives 3/3, 2/2, 3, and a
  PHP(9) failure **in 0.00 s** (versus ~38–60 s of search before it
  previously produced a wrong verdict).
- **Corpus gate (v2, full 209 rows)**: **159 verified / 19
  unknown-or-bail / 27 saturators**, 0 regressions vs the PINNED
  manifest, negative controls **8/8**. Row-by-row vs the #427 gate:
  **+1 `fuel-recursion-3/ob14` recovered** (it had been lost at #428),
  **0 losses**. The ledger is back to 159 — the same total as before the
  #427/#428 churn, but now with integer reasoning actually enabled.

## Follow-up backlog priority (2026-07-21, post-#428)

verus-fork's `2026-07-21-b191c71-CONFIRMED-...` reply (3 actionable leads +
2 questions) merged with the standing `engine_algorithmics_campaign`
follow-up pool into one ordered backlog. Ordering rule: soundness/
hardening first, then verus-fork-flagged live regressions (smallest/
best-understood first), then the existing perf/completeness pool by
effort and dependency (foundational items last since they may be
reshaped by what lands before them).

1. ~~**#427 re-investigation**~~ — **DONE 2026-08-02** (see the update
   above; root cause was the global `is_integer` logic-name gate, not
   the recorded EUF↔LIA framing). Two items were spawned by it and
   inserted into this backlog: **#429** (new, promoted to the top of the
   soundness tier below) and the **`ALL`-logic branch-and-bound perf
   cost**, which is no longer theoretical — it is now on the corpus
   critical path and is what cost `fr3/ob07` + `sv3/ob06`.

0a. **#429 — Int-sorted terms from other theories bypass integrality**
    (soundness-class false-SAT, 4 confirmed repros under dual z3∧cvc5
    oracle, orthogonal to #427). Same tier and rigor as #427/#428.

0b. **`ALL`-logic B&B perf** (newly corpus-critical): the correct-but-
    slow integer branch-and-bound path now runs for every Int-bearing
    obligation the corpus renders (which is nearly all of them, since
    `TheoryFlags::logic()` emits `ALL`). A cheap integrality pre-filter
    (e.g. a GCD test on non-strict bound pairs, which the adversarial
    lens showed would immediately settle two of its pathological probes)
    plausibly recovers `fr3/ob07` and `sv3/ob06` and may unlock more
    rows that integer reasoning can now reach. Highest-value perf item
    in the pool.
2. ~~**Q2 — class-level clause-removal invariant**~~ — **CLOSED
   2026-08-02** (oxiz `ad42391`; the base rate was right — it found a
   FIFTH, live instance in `vivify_clauses` the day it was installed).
3. ~~**Lead 2 — `fr2/ob13` D1 tier-2 ordering**~~ — **CLOSED 2026-08-02**
   (the recorded mechanism was wrong; see the Lead-2 update below).
4. **Lead 1 — ~~`dm3/ob03`~~ + `sv2/ob01` early abandonment** — **HALF
   CLOSED 2026-08-02, without being worked on.** `dm3/ob03` was
   recovered by the Lead 2 middle rung (3.4 s), attributed by
   kill-switch A/B; the remaining scope is `sv2/ob01` ALONE, which is
   `unknown` in all four kill-switch combinations, so neither Lead 2 nor
   #426 touches it. That `dm3/ob03` fell to a render-shape rung is
   itself evidence about the class: "gives up well under budget while z3
   proves both rendered scripts" was a RENDER-SHAPE sensitivity, not a
   capability regression. `sv2/ob01` should be re-investigated under
   that hypothesis first (it is also the fgr-simplex-bound row from the
   E2a profile, so item 9 may be the real owner).
5. ~~**#426**~~ — **CLOSED 2026-08-02** (oxiz `88c2679`; fired-but-
   insufficient parsed-trigger exemption made provisional). Corpus
   contribution measured at **+0 rows** — a pure soundness fix.
6. **Dt-as-App view upgrade** — `clean_mbqi.rs` TermView classifies
   datatype constructor/selector applications as Opaque; promoting them
   to real `App` views is the recorded recovery lever for the
   `dm2/ob03`-class rows E1's fix left as a saturator.
7. **EUF find-call-volume / canonical-args caching** — E2a's own
   conclusion (EUF-bound rows are call-volume-bound, not depth-bound;
   E2b was killed on exactly this basis) names the real lever.
8. **per-row additive-retry** — E1's `default∪additive=163` union
   showed additive mode wins rows default misses (and vice versa); a
   per-row retry policy could realize that union instead of the current
   global on/off.
9. **fgr simplex warm-start** (rank-4, measure-gated) — re-measure
   first (S's Trail infra + the trichotomy fix both changed the
   profile since the original 2026-07-16 measurement); implement only
   if the gate still holds.
10. **Work-bounded round emission** (foundational, large) — MBQI's
    round emission is deadline-bounded today; work-bounding it is the
    documented prerequisite for flipping S's Trail mode to default
    (currently opt-in because deadline-bounded emission reinvests freed
    throughput into fuel-flood-prone rows) and is a plausible shared
    root cause behind several of the churn patterns seen across E1/S/
    the trichotomy fix.
11. **V1 instantiation-trace replay** (largest, newest feature) — D1's
    on-disk memo store already reserves the schema (`instances: []`)
    for this; last because it is the most speculative/large-scope item
    with the least existing groundwork beyond the reserved field.

Lead 3 (`fr3/ob07`, 88.5s/90s guard margin) is **informational only** —
no action item, just a ledger-stability note for future sweeps.

Execution discipline unchanged from the rest of this campaign: each item
lands as its own commit, gated by the same rigor its risk class demands
(soundness items get randomized differentials at #428-scale; completeness/
perf items get the standing corpus-gate + suite discipline), main session
runs any corpus-scale sweep directly (setsid-detached).

**Update 2026-08-02 — Lead 2 (`fr2/ob13`) CLOSED, but NOT as an ordering
bug: the delegation ladder gained a third rung.**

The recorded framing ("the cap fires before the fallback is reached") does
not hold at the current pins. Measured with `ADSMT_DELEGATE_DEBUG=1` at
`OXIZ_MBQI_GUARD_MS=90000` (each `run_script` builds a FRESH `Context`, so
every rung gets its own full guard — `oxiz-solver/src/solver/mod.rs:816`):

| rung | script | wall | verdict |
|---|---|---|---|
| 1 | annotated (`:pattern`) | **1.6 s** | `unknown` (self-terminates, does NOT burn the guard) |
| 2 | floor (pattern-free, CURRIED) | **139.3 s** | `unknown` (guard-bound, 1.55× overshoot) |

The fallback *is* reached, in under two seconds. It is the FLOOR that
saturates — and z3 proves that very script `unsat` in **0.03 s**
(468 quant-instantiations), while it cannot prove the *annotated* one in
60 s. So reordering rungs 1 and 2 recovers nothing: 1.6 + 139.3 s blows
the 90 s per-row wall from either end. D1's tier-2 hint would not have
helped this row even with the memo enabled.

What DOES recover it: the floor is pattern-free **and** 1:1 curried —
two independent deltas from the annotated render, and OxiZ's trigger
inference reacts to both. The same obligation rendered pattern-free in the
annotated script's **re-collected** binder shape is `unsat` in ~9 s. That
render was previously never tried by anything (`ADSMT_DELEGATE_NO_PATTERNS`
produces it, but that is a triage kill-switch, not a rung).

So `proves_goal_impl` now runs **annotated → re-collected pattern-free →
curried floor**. The new middle rung is:

- **skipped entirely** unless its render is distinct from BOTH neighbours
  (no emitted pattern ⇒ identical to rung 1; no binder chain ⇒ identical
  to the floor — this is why `seq-vstd-1/ob08`/`ob09`'s single-binder
  fixtures still take the historical two-solve path in the unit suite);
- the **only budgeted** rung (`Context::set_timeout_ms`, a sixth of the
  effective `OXIZ_MBQI_GUARD_MS`, clamped to `[1 s, 15 s]` — 15 s under
  sweep-protocol v2), so the two load-bearing rungs keep the engine's own
  budget and the added wall is bounded;
- **strictly additive**: both original rungs still run, same scripts, same
  relative order, same budget. The completeness floor's guarantee ("every
  pre-feature `unsat` stays `unsat`") is untouched, and the trust story is
  the floor's own — the verdict is an OxiZ `unsat` on a faithful render of
  the same obligation (binder re-collection is `∀x.∀y.φ ⇒ ∀x y.φ`).
- `ADSMT_DELEGATE_NO_RECOLLECTED_FLOOR=1` restores the historical two-rung
  ladder byte-for-byte (the A/B baseline used below);
  `ADSMT_DELEGATE_SPEC_MS` overrides the budget.

**Measured (29 rows, guard 90 s, 90 s per-row subprocess wall, same binary,
kill-switch set vs unset):** `fuel-recursion-2/ob13` **timeout(91 s) →
`unsat` in 15.8 s**; 22 base-`unsat` rows all still `unsat`; **0
regressions**; 8 negative controls identical in both modes. Cost: bounded
by the budget, and paid only by obligations rung 1 fails to prove whose
shape is distinct — worst measured `+12.9 s` (`fr2/ob09`, `seq-vstd-1/ob09`
class: the middle rung proves what the floor would also have proved, more
slowly). Residual risk, stated honestly: a row that today verifies at
75-90 s could cross the wall. The slowest preserved `unsat` in the sample
was 21.7 s and the slowest baseline one 8.8 s, but only the full-corpus
sweep can price the tail.

**Update 2026-08-02 — joint gate for Lead 2 + #426: ledger 162, the
corpus's own high-water mark, with ZERO losses:**

Gated jointly (AD1 `97d52c7` + oxiz `88c2679`) on one binary, full 209
rows, sweep-protocol v2 (`OXIZ_MBQI_GUARD_MS=90000`):

```
verified            : 162      (159 -> 162)
unknown-or-bail     :  18
solver-timeout      :  25 (+4 skipped)
REGRESSIONS vs PINNED (unsat lost): 0
negative controls   : 8/8
```

Row-by-row vs the #27+#429 gate:

```
CONV  lost   : NONE
CONV  gained : datatypes-match-3/ob03, fuel-recursion-2/ob13, seq-vstd-3/ob08
SAT   lost   : fuel-recursion-2/ob13, seq-vstd-3/ob08   (both moved to CONV)
SAT   gained : NONE
```

**Attribution, measured — not assumed.** Because the two changes landed
under one gate, the three recovered rows plus `sv2/ob01` were re-run
across all FOUR kill-switch combinations on the same binary:

| row | BOTH ON | Lead2 OFF | #426 OFF | BOTH OFF |
|---|---|---|---|---|
| `datatypes-match-3/ob03` | `unsat` | `unknown` | `unsat` | `unknown` |
| `fuel-recursion-2/ob13` | `unsat` | `unknown` | `unsat` | `unknown` |
| `seq-vstd-3/ob08` | `unsat` | `unknown` | `unsat` | `unknown` |
| `seq-vstd-2/ob01` | `unknown` | `unknown` | `unknown` | `unknown` |

(`ADSMT_DELEGATE_NO_RECOLLECTED_FLOOR=1` / `OXIZ_MBQI_LAX_PATTERN_SAT=1`.)

So **all +3 belong to the Lead 2 middle rung, and #426 contributes +0
rows** — exactly the shape its structural argument predicts, and the
reason it could be landed as a pure soundness fix. The three prove in
3.4 s / 6.1 s / 8.5 s, all inside the rung's 15 s budget at this guard,
so the recoveries do not depend on the budget's ceiling.

Two of the three are not incidental:

- **`datatypes-match-3/ob03` was Lead 1's** (backlog item 4). It fell to
  a render-shape rung with no Lead 1 work at all, which reclassifies the
  lead: "abandons well under budget while z3 proves both rendered
  scripts" was RENDER-SHAPE sensitivity, not a capability regression.
  `sv2/ob01` remains, and is unmoved by all four combinations.
- **`seq-vstd-3/ob08` was an additive-mode-only row** in E1's
  `default ∪ additive = 163` union. It now verifies in the DEFAULT
  configuration. That is independent evidence for #426's own finding
  that additive's win on this class came from stripping the exemption
  (`augment_parsed_triggers` sets `augmented = true` unconditionally,
  and `augmented` already strips it), not from the added trigger groups
  — even though #426 is not itself what recovered this row.

The remaining union gap for per-row additive-retry (item 8) therefore
needs re-measuring against 162 before it is worth building.

**Update 2026-08-02 — #39 (EUF use-list never undone on pop) — ledger 169,
the two `#427` perf losses both recovered, 0 losses:**

Gate (v2, full 209 rows, oxiz `26d8d8a`):

```
verified            : 169      (162 -> 169)
unknown-or-bail     :  22
solver-timeout      :  14 (+4 skipped)     <- was 25
REGRESSIONS vs PINNED (unsat lost): 0
negative controls   : 8/8
```

Row-by-row vs the Lead 2 + #426 gate:

```
CONV  lost   : NONE
CONV  gained : datatypes-match-1/ob08, fuel-recursion-2/ob07,
               fuel-recursion-2/ob11, fuel-recursion-3/ob07,
               seq-vstd-1/ob06, seq-vstd-2/ob07, seq-vstd-3/ob06
SAT   gained : NONE
SAT   lost   : the 7 above, plus linear-euf-2/ob03, linear-euf-2/ob04,
               seq-vstd-1/ob03, seq-vstd-2/ob03
```

**Both rows `#427` cost us are back**: `fuel-recursion-3/ob07` (the row
verus-fork's Lead 3 flagged as a 1.5 s margin, which `#427` pushed from
88.5 s to 168 s and beyond) and `seq-vstd-3/ob06`. Disclosed in the same
breath: the four saturators that did NOT convert moved to
unknown-or-bail — they now SELF-TERMINATE as `unknown` instead of burning
the full 90 s guard. Those rows were never verified, so this is a cheaper
abstain rather than a loss, but it is a behaviour change and is recorded
as one.

The ledger trajectory is now 155 -> 158 -> 159 -> 162 -> **169**.

**The recorded cause for these rows was wrong, and that is the lesson.**
The `#427` entry above attributes `fr3/ob07`'s slowdown to "`ALL`-logic
Int problems now take the correct-but-slower LIA branch-and-bound path".
A symbol-resolved profile says 68.3% self in `EufSolver::propagate` and
~27% in libc memcpy: the row is EUF-bound. `#427` did not make B&B the
bottleneck — it raised the merge volume feeding an EUF structure that
grew FIBONACCI because nothing undid it on backtrack. Profiling first
would have found this two updates earlier. (The first profile attempt was
also wasted: the release profile carries no debuginfo, so it reported bare
addresses. `CARGO_PROFILE_RELEASE_DEBUG=1 CARGO_PROFILE_RELEASE_STRIP=none`
into a separate target dir is the recipe.)

**Two NEW pre-existing soundness bugs came out of #39's differential** and
are filed with repros here:

- **`430-euf-arith-implies-false-unsat*.smt2` — ground QF_UFLIA
  false-UNSAT.** The fatal class: adsmt trusts `unsat` only, so this is a
  direct path to a false `verified`. z3 AND cvc5 both answer `sat`.
  Minimal at 5 asserts, and it does NOT need push/pop — it reproduces
  flat. Localization so far: `(or (not A) p)` is `sat` (correct) while
  `(=> A p)`, `(= p A)` and `(ite A B true)` are `unsat`; pinning `A`
  true gives the correct `unsat` and pinning it false gives the correct
  `sat`, so BOTH branches are individually right and only the searched
  combination is wrong; replacing the arithmetic `>` with a pure-EUF
  disequality makes it `sat`, so the EUF<->arith interface is required.
  `theory_manager.rs`'s `suppress_stale_bounds` band-aid already
  describes this exact failure shape ("two distinct assertions of one
  atom under opposite polarities left in the simplex by a SAT backtrack
  the theory frame did not retract ... would be a spurious UNSAT").
- **`431-incremental-euf-false-sat.smt2` — incremental false-SAT**, not
  yet minimized.

Both reproduce on a pre-#39 binary AND on a pre-`#427` snapshot, so
neither is caused by this session's work.

**Update 2026-08-03/04 — #430 NOT LANDED. The ledger stays at 169 and the
submodule pointer stays at oxiz `26d8d8a`.**

The #430 fix (oxiz `90c17af` + measurement commit `4a5a425`) closes two
real false-UNSAT mechanisms and is verified correct — the repros flip to
`sat` in agreement with z3 AND cvc5, the genuine-`unsat` control still
answers `unsat`, and 2481 scoped tests pass. **It also costs 7 corpus rows**
(169 -> 162 verified, 0 regressions vs PINNED, negative controls 8/8; every
loss is `unsat` -> saturator, never a wrong answer). Among the losses are
`fuel-recursion-3/ob07` and `fuel-recursion-2/ob13`, both recovered earlier
the same day.

So the oxiz commits exist but **nothing points at them**: AD1's committed
pointer is still `26d8d8a`. Do not bump it until the redesign below lands.

**Two distinct pathologies, one per row family** — which is why looking for
a single explanation failed repeatedly:

- **Conflict-clause growth** (e.g. `fuel-recursion-3/ob12`, 1.9 s -> 110 s).
  `propagate_euf_equalities_to_arith` asserts an EUF-derived equality into
  the simplex as an unconditional fact; making the resulting conflict clause
  theory-valid means carrying the EUF explanation, and that explanation
  grows with the proof forest. Measured with `OXIZ_EUF_EQ_DBG=1`: average
  clause length 7 -> 23 literals, peak 60, over 128 conflicts, with
  `arith_terms = 428` and 116,797 EUF-equal pairs handed to the simplex.
  Longer clauses learn less, so more conflicts follow, so the explanation
  grows again. The precise per-conflict filter (only equalities whose
  `assert_eq` reason term appears in the arithmetic conflict) does not stop
  it.
- **The `term_to_node` trail** (e.g. `fuel-recursion-2/ob13`). Erasing the
  mapping on every pop forces re-interning. `OXIZ_EUF_NO_TERM_TRAIL=1`
  alone restores the row: 165 s `unknown` -> 4.8 s `unsat`, against a 5.0 s
  baseline.

**The redesign both want:**
- Clause growth: proper Nelson-Oppen theory propagation — propagate the
  equality as a LITERAL with its explanation and let the SAT layer own it,
  instead of asserting it into the simplex as an unconditional fact. This
  is what z3 and cvc5 do and it makes the reason structurally correct
  rather than reconstructed after the fact.
- Trail: O(1) scope-stamped invalidation, or trailing only the mappings
  created by a `sig_table` congruence hit (the only ones that can be wrong)
  — not erase-and-reintern.

**Methodology failures from this investigation, recorded so they are not
repeated.** Four causes were reported and all four were wrong. The common
root was never verifying that the comparison being run was the comparison
intended:

1. A stale binary was measured three times: a `CARGO_TARGET_DIR` override
   sent the build to one target directory while `cp` copied from another.
   The build "succeeded", so the `&&` guard did not catch it, and the three
   configurations were byte-identical (proved afterwards by md5).
2. A file-level bisect used the wrong per-file baseline — `HEAD` already
   contained both changes, so it only bisected the later refinements. The
   corrected version then failed to build at all, because `explain_equality`
   being made `pub` couples the two files.
3. A "0 conflicts" instrumentation reading retired the CORRECT hypothesis
   for hours; re-instrumenting showed the site fires constantly.
4. Machine contention was suspected and should have been dismissed
   immediately — the baseline binary held 2.0 s under the same load.

Rule adopted: **every A/B prints the md5 of each artifact before measuring
it**, and a kill-switch A/B is only trusted after the switch is shown to
change the measured quantity on at least one input.

**Update 2026-08-04/09 — #430 stays OPEN. Revisit the landing decision when
a cost reduction lands, not before.**

Three redesigns were built and measured after the first attempt; none
recovered the cost. The submodule pointer stays at oxiz `26d8d8a` and the
ledger stays at **169**.

| attempt | oxiz commit | rows lost (of 8 candidates) |
|---|---|---|
| alias + undo trail | `90c17af` + `4a5a425` | 8 |
| in-scope congruence as a MERGE | `b92ebe4` | 8 |
| narrowed alias rule + star injection + one arith check | `d09f990` | 7 |

The third attempt did close the last open MECHANISM: expressing an in-scope
signature hit as a retractable merge (rather than as permanent node
identity) makes `corpus-triage/430-407-*.smt2` answer `sat`, agreeing with
z3 and cvc5. **All three #430 mechanisms are now understood and fixed** —
what is unresolved is only what they cost.

**The shared premise of all three designs is false on the worst row.** Star
injection cut the injected equalities 116,797 -> at most 428 and the LIA
branch-and-bound invocations from N to 1; `fuel-recursion-3/ob12` moved
109.1 s -> 109.0 s. The cost is not the scan volume.

**How bad the loss actually is** (GATE 0, 10x guard): six of eight rows
recover at 1.0-2.5x the baseline wall — `fuel-recursion-2/ob13` is FASTER
than baseline and `seq-vstd-1/ob06` is 1.0x — and only `fr3/ob12` and
`fr3/ob14` fail even at 1000 s. These are wall-clock-guard timeouts, not a
learning collapse.

**Why open rather than landed.** The precedent points the other way (#427
cost 2 rows and #428 cost 3, both landed as mandatory correctness), and
#430 is a genuine false-UNSAT — a silent false `verified` under verus's
negate-and-refute discipline. The call was made deliberately: at 6-7 rows
the cost is large enough, and the ledger is mutually pinned with verus-fork
closely enough, that it waits for a cost reduction. #430 is disclosed to
verus-fork as unfixed (AD1 `2565cea`) and stays disclosed.

**Gating condition for revisiting: a landed cost reduction.** Re-run the
eight rows above; if they come back within the 90 s protocol guard, land
#430 and file the re-pin. Candidate levers, in the order the evidence
supports:

1. **Measure the LEARNT clause, which nobody has.** `avg_lits` in the
   `OXIZ_EUF_EQ_DBG` output counts the theory conflict SET.
   `analyze_theory_conflict` skips level-0 literals entirely and pushes only
   LOWER-level ones into `learnt`, so the learned clause is strictly shorter
   and has never been instrumented. The whole "clause growth" story rests on
   the wrong number.
2. Exact attribution by arith reason ID rather than by `TermId` — make
   `assert_eq` return its `add_reason` id and filter the cited equalities by
   the ids the conflict actually used.
3. Nelson-Oppen proper: propagate the equality as a literal carrying its
   explanation instead of asserting it into the simplex as an unconditional
   fact. Two structural blockers are recorded: a theory cannot mint an atom
   mid-solve (`TheoryHooks` methods take no solver handle, and `term_to_var`
   is moved into the TheoryManager which is moved into the Trail), and
   `solve_with_hooks_inner` treats an `Undef` propagated literal at
   `final_check_complete` as `Sat`.

Everything needed to resume is committed: three repros, four kill-switches
(`OXIZ_EUF_ALIAS_IN_SCOPE`, `OXIZ_EUF_NO_TERM_TRAIL`,
`OXIZ_NO_ARITH_EQ_REASONS`, `OXIZ_EUF_EQ_DBG`), and the scan/conflict
instrumentation.

**Update 2026-08-17 — #431 LANDED. Ledger 169 -> 171, the corpus's own
high-water mark, with zero losses and zero regressions.**

Two soundness fixes, both false-SAT, both closed on top of the 169-ledger
baseline oxiz `26d8d8a`:

- **`6f8e54f`** — `Solver::pop` cleared `trivially_unsat` unconditionally,
  so a BARE matched `(push)(pop)` discarded a level-0 contradiction:
  `(assert p) (assert (not p)) (check-sat)` answered `unsat`, and after
  `(push 1) (pop 1)` the same query answered `sat`. `add_clause`'s
  `level == 0` arm sets that flag and stores NO clause, so the flag is the
  only record and clearing it left nothing to re-derive. Seventh member of
  the pop-scrub family. Upstream v0.3.2 is also wrong here (it answers
  `unknown`), so there was nothing to backport.
- **`5cbff16`** — `propagate` batched its signature publications until after
  the use-list scan, so two parents acquiring the SAME signature in one merge
  event never saw each other and their congruence was never enqueued. Three
  lines of QF_UF at level 0. Publishing eagerly is what upstream does, and it
  is where the differential found the bug. **A test was pinning this bug**:
  it asserted "batched updates must not detect the in-burst hab/hba
  collision", i.e. it required the engine NOT to notice a congruence that
  genuinely holds — a behaviour-identity pin is only as sound as the
  behaviour it was snapshotted from.

```
verified            : 171   (169 -> 171)
unknown-or-bail     :  20
solver-timeout      :  14
REGRESSIONS vs PINNED: 0
negative controls   : 8/8

CONV lost   : NONE
CONV gained : divmod-real-2/ob05, seq-vstd-3/ob05
```

Trajectory: 155 -> 158 -> 159 -> 162 -> 169 -> **171**.

Removing the batching was expected to cost a constant factor and instead
GAINED time: `fuel-recursion-1/ob06` 10.9 s -> 7.0 s, `seq-vstd-1/ob06`
15.9 s -> 11.2 s, `seq-vstd-2/ob07` 15.3 s -> 13.0 s. Catching a congruence
earlier prunes more than the saved hash lookups cost. Disclosed alongside:
`seq-vstd-2/ob03` moved from unknown-or-bail to saturator — it now burns the
guard instead of self-terminating. Never verified, so not a loss, but a
behaviour change.

**A CONFOUNDED MEASUREMENT NEARLY KILLED BOTH FIXES, and how it was caught
is the part worth keeping.** An earlier attempt gated this pair at
**169 -> 155 with THREE regressions against the pinned manifest** — the
first non-zero PINNED regression of the whole campaign — and a follow-up
attribution A/B then blamed the pop-scrub half, reporting rows going from
2.8 s to 112 s. Both results were artefacts: the submodule under test was
`1ff42a6`, which carries the four **#430** commits as well, and #430's cost
(independently measured at 6-7 rows and deliberately NOT landed) was being
charged to #431. The only clue was that saving and restoring a single `bool`
at `push`/`pop` cannot cost 100x, and that the direction was wrong anyway —
a preserved `trivially_unsat` makes `solve()` return EARLIER, not later.
Re-measuring each fix alone on a clean `26d8d8a` baseline showed both are
free. The rule this adds to `feedback-ab-verify-the-artifact`: verifying that
two binaries DIFFER is not enough; verify that they differ **only** in the
change under test. `git log <baseline>..<candidate>` before every A/B.

#430 is preserved on the oxiz branch `0.2.4-wip/430-not-landed` (tip
`1ff42a6`) and stays unlanded — its own gating condition (a landed cost
reduction) is unchanged.

**Update 2026-08-17 (later) — five oxiz commits landed, ledger UNCHANGED at
171 with 0 regressions, which is the result they were predicted to have.**

Submodule `5cbff16` → `e9c43a0`. Gate: **171 verified / 20 unknown-or-bail /
14 saturators**, 0 regressions vs PINNED, negative controls 8/8, class
distribution identical to the 171 gate above.

The prediction was made BEFORE the gate and is worth recording as the reason
the gate was still run: `render_smtlib` emits exactly one non-assertion
command, `(set-logic ALL)` — no `define-fun`, no `set-option` — so none of the
parser or lexer fixes below can reach a rendered obligation, and the work
budget ships default-off. Predicting no change is not the same as measuring it.

- **`85b2018`** — `OXIZ_MBQI_ROUND_DBG`, one line per instantiation round.
  `OXIZ_MBQI_DBG` prints per LEMMA with no round or time axis, so it shows what
  was instantiated and never the RATE. Immediately showed that emission is
  geometric within an episode and that `seq-vstd-2/ob03`'s LAST round consumes
  **40.0 s of a 90 s guard alone**, emitting 3,643 instances. The 100-round cap
  never binds (2 to 7 rounds per episode); the wall deadline binds INSIDE a
  round where the loop-top check cannot see it.
- **`4d8f9d7`** — lexer progress guarantee, BACKPORTED from upstream 0.3.3
  (its only substantive solver-side change past v0.3.2). A character that can
  neither start nor continue a symbol made `read_symbol_chars` consume nothing,
  so `next_token` minted the same zero-width token for ever. `,` suffices. This
  HANGS the parser: the unknown-command recovery in `parser/commands.rs` pulls
  tokens until depth zero or `Eof`, and neither arrives. Two binaries differing
  only in that file: `rc=124` before, `sat` after, `unsupported` + `sat` from
  z3.
- **`677b5ea`** — **#432**, `define-fun` formals stayed FREE in the expansion.
  Found by testing upstream v0.3.2's release notes against this fork. Upstream
  reports it as "arguments could silently vanish"; the direction they do not
  name is worse — two calls that should be independent collapse into ONE shared
  constraint, so `(isfive 5)` and `(not (isfive 6))`, both trivially true,
  become `(= k 5)` and `(not (= k 5))` and the script reports **`unsat`**. A
  false `unsat` is a false proof. Mechanism confirmed by a discriminating
  triple in which TWO of three cases used to pass by coincidence (the `Bool`
  fallback sort; a formal name colliding with a same-sorted global, which the
  hash-cons then aliases).
- **`8395934`** — every NUMERIC `set-option` value was silently dropped
  (`expect_symbol().unwrap_or_default()`), so `(set-option :timeout 5000)` set
  nothing and said nothing. Found because a new numeric option worked through
  its env var and not through `set-option`.
- **`e9c43a0`** — **#35**, work-bounded round emission, default OFF. See the
  census file for the calibration.

**The census is the durable artifact here**
(`2026-08-17-mbqi-instance-census.tsv`): verified rows peak at **1,554**
accumulated instances, the unverified side reaches **74,199**. No verified row
reaches 2,000, so a budget there cannot regress one — provable from the
measurement rather than hoped for.

**Why #35 is the gate on the remaining perf backlog.** A re-profile after
#39/#431 killed one backlog item and re-aimed the rest. `EufSolver::propagate`,
once 68.31% self, is now **1.67%** — that figure was a symptom of the #39
Fibonacci defect, and the EUF find-call caching item built on it is worth under
2% and is closed as measurement-killed. What the profile shows instead, on
`fuel-recursion-2/ob07` (41 s): simplex **45.4%** self, of which
`update_assignment` is **26.7%** (it recomputes the whole assignment on every
pivot where Dutertre-de Moura's `pivotAndUpdate` is O(column nnz)), plus
`Simplex::push`'s `tableau.clone()` at **7.24%** and `pop`'s stale-row scrub
`retain` at **7.20%** — both `BacktrackMode::Snapshot`-only paths that
`Trail` removes by construction. On `seq-vstd-1/ob06` (11 s) the shape is
different again: `ast::manager` term construction **15.8%**, EUF **1.15%**.

Every one of those is a pure speedup, and a pure speedup is exactly what
drowned five fuel-recursion rows in the 2026-07-19 `Trail` A/B: under a
deadline-bounded loop the freed throughput is reinvested into more
instantiation per window instead of into finishing earlier. Until emission is
work-bounded, each of these levers is a coin flip against the corpus.

**Update 2026-08-23 — #433 (2 of 3) CLOSED: Bool truth values now reach EUF.
Ledger 171, zero regressions, row-identical to the previous gate — after a RED
first gate whose attribution REDESIGNED the fix.**

Submodule `e9c43a0` → `246657d`. Two of the three false-SAT families the
v0.3.2-notes battery found in this fork are closed:

- `(= b1 b2)` with `h(b1) = 1`, `h(b2) != 1` reported `sat` — the Bool
  equality was a Tseitin iff gate only, invisible to congruence.
- `p, q, (not (= (k p) (k q)))` reported `sat` — a Bool ARGUMENT's truth
  value never reached EUF at all (`BoolApp` completes application RESULTS
  only).

**The first attempt gated RED, and the A/B is the story.** Implementing both
of upstream's fixes (a `Constraint::Eq` registration per Bool equality + the
argument watches) measured **171 → 165 with one PINNED regression** — the lost
rows all long ones. A four-way kill-switch A/B on one binary put the ENTIRE
cost on the equality registration and none on the watches (`fr1/ob06` 7.4 s →
21.6 s under eq-registration, 7.4 s under watches-only; `fr2/ob07` 42 s →
guard-out vs 42 s). And the watches SUBSUME the equality registration for
completeness, because Bool is a TWO-VALUED domain: equality is value
agreement — the iff gate forces equal operands to one value, the watches land
both nodes in the same canonical class; unequal operands land in the two
mutually-disequal classes. An operand with no watch never appears as a UF
argument, participates in no congruence signature, and has nothing to tell
EUF the gates don't already tell the SAT core. So the equality registration
was REMOVED, not tuned: the final mechanism is one `Constraint::BoolValue`
watch per Bool-sorted UF argument (polarity-folded), plus tying the
`true`/`false` LITERALS to the canonical bool nodes in both intern paths (two
routes to "true" used to land in two disjoint classes).

Final gate: **171 / 20 / 14, 0 regressions vs PINNED, negative controls 8/8,
row-identical** to the previous gate — the soundness completion costs the
corpus nothing. The equality-family regression tests all pass on the value
route alone, which is the subsumption argument checked rather than believed.

Remaining from the battery: **05 only** — the non-convex arith⇄EUF case split
(`1 <= x <= 2`, `f(1) = f(2) = a`, `(not (= (f x) a))` reports `sat`;
upstream bounds an explicit `(or (= t lo) … (= t hi))` split at span ≤ 12,
≤ 48 terms/round). Exposure: CLI/direct SMT-LIB only — the adsmt delegation
trusts `unsat` alone in every one of these families.

**Update 2026-08-23 (later) — #433 (3 of 3) CLOSED: bounded int case split.
The v0.3.2-notes battery is now 12/12 against z3. Ledger 171, row-identical
again.**

Submodule `246657d` → `a970703`. The non-convex arith⇄EUF gap (`1 <= x <= 2`,
`f(1) = f(2) = a`, `(not (= (f x) a))` was `sat`) closes with a conditional
LIA-tautology case split (span ≤ 12, ≤ 48 terms/round, ≤ 8 rounds,
`OXIZ_NO_INT_CASE_SPLIT` kill-switch), fed by an assert-time unit-bound
journal in `ArithSolver` — the simplex can't answer "the asserted bounds of
x" because every constraint lives behind a slack variable.

Verified by an 800-seed randomized z3 differential (the standing rule for a
change that can mint a new `unsat`): fabricated-unsat 0, A/B divergence 0,
gap instances closed 342. The 54 remaining our-sat/z3-unsat rows are 49
spans above the cap (by design) plus **5 cross-linked spans = #434**, a real
residual: a split disjunct set by CLAUSE ASSIGNMENT does not push a linked
variable's entailed fix into EUF, though the same equality asserted as a
unit refutes the model. Repro committed as
`434-arith-euf-arrangement-model-equal-not-entailed-false-sat-OPEN.smt2`;
the feature is sound with the bug present (it only under-closes).

**CORRECTION 2026-08-30 — #434 was misattributed above, and to the split, and
in the commit message that landed it.** It is NOT caused by the case split and
NOT a clause-assignment defect: `OXIZ_NO_INT_CASE_SPLIT=1` answers `sat` on
every #434 repro, so the bug PRE-DATES #433 by an unknown margin and rides on
every ledger back through 143. What the split's differential did was find it.

The real defect is the **Nelson-Oppen arrangement obligation**, undischarged.
`(get-value ...)` on the accepted model returns `x0 = 4, x1 = 3, (f0 3) = 0,
(f0 x1) = 1` — the arithmetic is satisfied and the UF is **not a function**.
`x1` and the literal `3` carry the same arithmetic value; nothing ever tells
EUF they are equal, so their `f0` images are free to differ.
`model_based_combination` propagates only ENTAILED (fixed) values, and here
x1's value is model-CHOSEN, so it is never reconciled.

The earlier reading — "a level-0 equality goes missing from the re-solve's
arith state" — was **wrong**, and wrong in the way this session has already
been burned twice: a debug trace was read without confirming which `TermId`
each line named. `(get-value)` on the model settles in one command what the
trace could not, and should have been the first move. The `OXIZ_MBC_DBG`
trace added for it is still useful, but its earlier interpretation is retracted.

Two repros added alongside: `434-min-arrangement-*.smt2` (smaller, one
function) and `434-control-directly-bounded-is-closed.smt2` — the same shape
with the shared variable bounded DIRECTLY, which #433 already closes. The
contrast is the diagnosis: the solver reconciles a shared term it can FORCE
and cannot reconcile one it merely AGREES with.

Gate: **171 / 20 / 14, 0 regressions, negative controls 8/8, row-identical**
to both preceding gates. Trajectory unchanged at 171 — every #433 closure was
soundness-side, none of the corpus rows sat on these gaps.

**Update 2026-08-30 — #434 root-caused, #435 found, and the fix for #434 is
deliberately NOT enabled. Ledger 171, row-identical for the fourth gate running.**

Submodule `93729f5` → `fd2ea4a`. One default-on fix, one default-off finding.

**LANDED (default on): the fixed-value probe could report ANY term as fixed.**
`ArithSolver::fixed_value_with_reasons` proves `t = v` by asserting `t >= v+1`,
checking for infeasibility, popping, and repeating below — and never checked
that the conflict USED the probe's own bound. Against an already-infeasible
state every probe returns `Unsat` regardless, so every term reads as "fixed" at
whatever `value()` last returned, with a reason set that omits the literals the
caller then builds a conflict clause from. Measured: that clause refuted a
satisfiable branch the search had not yet reached. The guard is that the
explanation must mention the probe's own bound.

**NOT ENABLED: `SolverConfig::persist_const_index`.**
`interned_int_constants` maps an integer VALUE to its canonical EUF node, and
is rebuilt EMPTY on every `TheoryManager` construction — once per iteration of
`check_level`'s loop — while `euf` is carried forward. Since
`intern_term_for_congruence` returns early for a term EUF already interned, a
value registered in round 1 can never re-register, so from round 2 on the index
is permanently empty and BOTH of its jobs stop: `model_based_combination`'s
entailed-value merge and the pairwise constant-disequality edges. The struct's
own comment calls this "scratch state ... reinitialised every round"; it is not
scratch, it is a derived index over `euf`.

Carrying it forward closes #434's repros — and opens a false `unsat`: 2
fabricated refutations per 200 seeds of the new `arith_euf_merge_diff.py`,
against 0 with it off. So it ships OFF. **A completeness bug in the `sat`
direction is strictly preferable to a false proof**, and that is the whole
decision.

**#435, the unsoundness that exposed.** Reduced to a script with no case split,
no quantifiers and no push/pop: assert a VALID clause after a `(check-sat)` and
re-solve, and the second `(check-sat)` answers `unsat` where the same clause
present from the start answers `sat`. All six theory conflict clauses emitted on
that run were hand-checked as valid lemmas and none was empty, so the refutation
is assembled somewhere this investigation did not reach — propositional level,
not MBC. Repros committed; the cause is open.

**#434's cause was recorded WRONG twice before this.** First as a clause-
assignment defect, then as a missing level-0 equality. `(get-value)` on the
accepted model settled it in one command — `x0 = 4, x1 = 3, (f0 3) = 0,
(f0 x1) = 1`, i.e. the arithmetic holds and the UF is not a function — and
should have been the first move both times. The retraction is `4e08e29`.

**What actually closes #434**, per a 9-agent design review: ACKERMANN lemmas
`(or (not (= a_i b_i)) ... (= (f a) (f b)))`, valid in FOL with equality and so
independent of the model, the decision level and every value map. No merge, no
probe, no `terms_to_conflict_clause`. The review rejected the merge-based
approach for exactly the reason measured here. It also found
`ArithSolver::derive_shared_equalities` (solver.rs:1235) — a complete
model-bucketed care graph that is DEAD CODE, reachable only from its own tests
because `TheoryCombination::get_shared_equalities` takes `&self` and cannot
probe.

Two design notes land alongside, on the user's architectural read that
dependence on delegation itself has to come down:
`DELEGATION_TRUST_REDESIGN.md` (the trust posture is backwards — a delegate
false-`sat` costs adsmt nothing, a false-`unsat` stamps a proof, and 2 of the 3
false-UNSATs found this month are OPEN) and `NATIVE_VIA_LUKB_STRUCTURE.md`
(37.1% of the corpus's 45,013 axioms are fuel unfolding, 19.5% mention
`has_type` — both structures adsmt already holds and pays MBQI to re-derive).

**Update 2026-08-30 (#37 checkpoint) — the three OPEN items, measured against
the SHIPPED DEFAULT rather than described.**

"OPEN" alone does not tell a downstream whether it is exposed. So all three
were run on the stock `fd2ea4a` release binary (md5
`efaab848de27bdcc4c94a85167a75c54`, no options set) and cross-checked against
z3 and cvc5:

```
repro                                             oxiz     z3     cvc5   direction
430-euf-arith-implies-false-unsat-minimal         unsat    sat    sat    FALSE-UNSAT
430-407-level0-node-collapse-false-unsat-OPEN     unsat    sat    sat    FALSE-UNSAT
434-min-arrangement-false-sat-OPEN                sat      unsat  unsat  false-sat
434-arith-euf-arrangement-...-false-sat-OPEN      sat      unsat  unsat  false-sat
435-min-assert-after-checksat-...-OPEN            sat sat  sat sat sat sat  (agrees)
```

The row that changes a downstream's risk assessment is the last one: **#435 is
NOT reachable at the shipped default.** What exposed it was
`persist_const_index`, and that flag ships OFF precisely because turning it on
minted false proofs. The open cause remains worth finding — but it is not
currently anyone's exposure, and saying so is part of an honest disclosure.

#430 is the opposite: still live, still the fabricated-proof direction. #434 is
a false-`sat`, which costs adsmt nothing under the current trust posture (a
delegated `sat` is already treated as "no delegation") — it is a real
combination gap, not a live risk.

Disclosed to verus-fork in
`.local-replies-to/verus-fork/2026-08-30-repin-fd2ea4a-soundness-exposure-measured-and-ledger-definition-question.md`,
together with a proposal to change what the shared 171 MEANS (from "the
delegate said `unsat`" to "a checked `unsat`") — a change that needs their
agreement because the number is mutually canonical, and one whose floor is now
known to be 90 rather than 0.

**Update 2026-08-30 — #430 re-reviewed on the CURRENT baseline, per the
standing instruction to revisit "when something that reduces its cost lands".
It stays unlanded, and the profile says the next attempt should aim somewhere
else than the last three did.**

Several things that plausibly relieve it HAVE landed since the cost was
measured — #39 (the EUF use-list growing fibonacci across backtracks), #433's
case split, the fixed-value probe guard. So the fix was rebased onto `fd2ea4a`
(branch `0.2.4-wip/430-remeasure`, cherry-picking the two #430-unique commits;
the old branch's #431 and push/pop commits are already on the mainline) and
re-measured.

Artifacts, per the A/B discipline: `adsmtc-baseline`
`0ed689517f43986b67b4161db707e08b` vs `adsmtc-430fix`
`6a4fd0c8f7c707ac31c00fc14f490813`, differing by exactly
`git log fd2ea4a..6476ac7` = the two #430 commits.

**Correctness: the fix still works.** Both #430 repros answer `sat` under it,
matching z3 and cvc5.

**Cost: not recovered.** `OXIZ_MBQI_GUARD_MS=90000`, three candidate rows:

```
row                     baseline        430fix
fuel-recursion-2/ob13   4,754ms unsat   112,509ms unknown    LOST
fuel-recursion-3/ob07  19,420ms unsat    82,484ms unknown    LOST
seq-vstd-3/ob06         8,427ms unsat     6,638ms unsat      kept
```

Two verdicts lost on three probes, so the ledger drops and the decision is
unchanged: **do not land.** The full 209-row gate was NOT run — it would only
refine "how many rows" for a decision that two lost rows already settle, and it
costs hours of idle machine. Saying so beats implying a sweep happened.

**Attribution (kill-switches, on `fuel-recursion-2/ob13`):**

```
merge, term_trail on  (default)   115,829ms unknown
merge, term_trail off             116,225ms unknown   <- trail is FREE
alias + term_trail                 13,159ms unsat
alias, no trail                    35,621ms unknown
```

`term_trail` costs nothing (115.8 vs 116.2 s). **The whole cost is the merge
mechanism** — expressing an in-scope signature hit as a fresh node merged with
the existing one, instead of aliasing.

**But the cheap configuration is NOT a substitute, and this is the new fact.**
`alias + term_trail` is 9x faster and keeps the verdict — and closes only ONE
of the two #430 repros. `430-407-level0-node-collapse` still answers `unsat`
against `sat` from both oracles. Only the merge mechanism closes both. So the
trade is not "same fix, cheaper spelling"; the cheap spelling is a weaker fix.

**Where the cost actually is: SIMPLEX, not EUF.** `perf` on the 115 s run
(22,447 samples):

```
36.78%  arithmetic::simplex::Simplex::update_assignment
18.31%  arithmetic::simplex::Simplex::check
 5.68%  SmallVec::retain
 3.99%  HashMap::retain
 3.34%  Ratio<T>::cmp
```

55% in simplex plus ~8% in rational arithmetic. The merge mechanism is not
slow because EUF does more work — it is slow because each in-scope signature
hit mints a NEW EUF node, and every new node is another term the EUF→arith
equality propagation hands to the tableau. The blowup is in the arithmetic
interface the extra nodes create.

That redirects the next attempt. The three redesigns already tried (star
injection, single arith check, narrowed alias rule) aimed at the EUF side. The
lever the profile points at is **not minting the node when the congruence is
already justified at level 0** — those aliases are permanent and need no
retractable form, and each one avoided is one fewer tableau entry. Whether
that recovers the cost depends on what fraction of in-scope signature hits are
level-0-justified, which is a measurement nobody has taken.
