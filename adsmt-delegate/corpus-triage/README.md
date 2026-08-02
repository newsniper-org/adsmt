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
2. **Q2 — class-level clause-removal invariant** (verus-fork's own
   question: #428 is the 4th independent recurrence of the clause-id-
   recycle stale-watcher class; base rate says a 5th is likely — design
   a systemic device, not another one-off site fix).
3. ~~**Lead 2 — `fr2/ob13` D1 tier-2 ordering**~~ — **CLOSED 2026-08-02**
   (the recorded mechanism was wrong; see the Lead-2 update below).
4. **Lead 1 — `dm3/ob03` + `sv2/ob01` early abandonment** (both give up
   well under the 90s budget while z3 proves BOTH rendered scripts
   unsat — a completeness-floor-stage capability regression, not a
   budget problem; root cause not yet known, needs investigation before
   a fix shape is clear).
5. **#426** — fired-but-insufficient parsed-trigger exemption spurious-
   sat class (E1 finding, standalone-OxiZ, adsmt shielded by
   never-trust-sat) — decide + close.
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
