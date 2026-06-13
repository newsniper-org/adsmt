---
name: oxiz-redesign-verification-pipeline
description: "OxiZ SAT-core §4 redesign verification pipeline — [pre-verify (Verus model) → implement Phase 1 → post-verify (Verus on real code)]; pre-verification (L2 + UNSAT soundness) DONE and verifying"
metadata:
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

User-chosen workflow for the [[oxiz_sat_core_redesign]] §4 redesign (decided 2026-06-13):
**`[선검증 → 구현체 작성 → 후검증]`** — formally verify the DESIGN first, then implement Phase 1, then formally
verify the IMPLEMENTATION.
- **Pre-verification scope = L2 + UNSAT soundness** (NOT full L3 1-UIP correctness). Standalone Verus MODEL of §4.
- **Implementation = Phase 1** on OxiZ branch **`0.2.4-redesign`** (forked from `0.2.4-feat/cdqi` @ `3312eb5`).
- **Post-verification = L4** — Verus-annotate & verify the REAL `oxiz-sat` code (after Phase 1).

**Tooling:** upstream Verus via AUR (`verus-bin` `0.2026.06.07`, `cargo-verus`/`vstd`/`verusfmt` at `/opt/verus`).
NOT the adsmt-fork Verus (avoids circularity — don't verify OxiZ with a tool that delegates to OxiZ). A
cargo-verus lib needs an empty `[workspace]` in its Cargo.toml or it gets pulled into AD1's workspace.

**Submodule:** `external/oxiz-sat-redesign-verification` — ALREADY declared in AD1 `.gitmodules`
(url `github.com/newsniper-org/oxiz-sat-redesign-verification`, branch main); the user pre-created the empty repo
(`5290f32` + placeholder.md). I populated it with the cargo-verus pre-verification project.

**PRE-VERIFICATION STATUS: DONE — `cargo verus verify` → 28 verified, 0 errors, no `assume`/`admit`/`external_body`.**
Four src files (proved on a model, not the engine):
- `spec.rs` — propositional semantics (Lit/Clause/Formula, satisfiable, entails) + UNSAT-soundness foundation
  (`entails_empty_implies_unsat`, `entailed_clause_preserves_models`).
- `trail.rs` — §4.1 lock-step `frames.len()==level+1` preserved by the two HOOKED level-mutators
  (`new_decision_level`/`backtrack_to`); §4.3 typed `Reason` (TheoryLemma carries non-null asserting lit ⇒
  placeholder unrepresentable); **`backtrack_to_size_bypass_breaks_lockstep`** = PROVED negative result that the
  real engine's other two `current_level` writers (`backtrack_to_size`/`clear`, the §4.1 four-writer gap) DO
  desync — pins the residual instead of hiding it.
- `analyze.rs` — §4.4 robustness: S1 no var-0 placeholder, S2 empty⟺level-0-root, S3 degenerate conflict routes
  to guard (BUG 2), S4 `decide` is a proof fn with `requires bcp_fixpoint` (BUG 3 unrepresentable at API) +
  `settle` models fixpoint-restore; **bridges** `analyze_degenerate_entailed`/`analyze_uip_entailed` connect
  analyze output to entailment.
- `soundness.rs` — `resolution_sound` + `valid_derivation`/`derivation_entailed` (strong induction) +
  **`refutation_implies_unsat`** (ANY resolution derivation reaching ∅ ⟹ unsat — the gold-standard
  spurious-UNSAT-is-impossible result, entailment PROVED from derivation validity, not assumed).

**PROCESS — adversarial audit is mandatory for formal-verification artifacts.** A 3-agent audit (vacuity/mutation,
faithfulness, proof-chain) found the first cut gave assurance NARROWER than its prose: the 1-UIP `uip` was
grounded-by-fiat (S1 assumed its conclusion on the UIP branch), analyze output was never linked to `entails`
(soundness premise merely assumed), and the lock-step corollary over-claimed (named incremental-pop as covered
when it bypasses the hook). I STRENGTHENED rather than just caveated: added the resolution-derivation soundness
chain (entailment now proved), the analyze→entails bridges, and the four-writer negative result; README states the
honest limits (it's a MODEL; uip abstract; backtrack_to_size/clear + the settling loop are L4 obligations).
CAUTION: an audit subagent (general-purpose, write access) left a MUTATION PROBE in the REAL `spec.rs` (removed a
lemma call) — when auditing with write-capable agents, instruct them to use /tmp copies AND re-check the real tree
for leftover edits afterward.

**PHASE 1 IMPLEMENTATION: DONE on `0.2.4-redesign`** (`e1bff29` typed-Reason+trail-driven-hooks, `0f3c3f6`
TheoryHooks-driver+toy-theory, `e6d7bf8` differential-fuzz+fix). The §4 contract is landed in real `oxiz-sat`,
ADDED IN PARALLEL to the legacy `TheoryCallback`/`solve_with_theory` (untouched → SMT path stays green). A Plan
agent produced the 9-step plan (each step builds green); key facts: oxiz-sat has NO parallel level_stack to delete
(that's oxiz-solver = Phase 2); `Reason::Theory`/`assign_theory` were near-dead. Landed:
- §4.3 `Reason::TheoryLemma(TheoryReasonId)` + `TheoryReason{asserting, explanation}` store on Trail.
- §4.2 `TheoryHooks` trait (6 methods, object-safe, **`Send+Sync`** — required because `Theory` in oxiz-theories
  is Send and Bv/FpSolver embed a Trail) + `TheoryStep{Ok/Propagate/Conflict}`.
- §4.1 `Trail.theory: Option<Box<dyn TheoryHooks>>`; hooks fire from inside ALL FOUR level-writers
  (`new_decision_level`/`backtrack_to_with_callback` + the proven-bypass `backtrack_to_size`/`clear`). restart
  routes through `backtrack_with_phase_saving`→`backtrack_to_with_callback` so it fires hooks (fe71e93 hazard gone).
  `set_theory` SYNCS the theory with the current trail (replays frames+assignments) — else pre-install level-0
  units are invisible (caught by a unit test).
- §4.2 `solve_with_hooks` driver (final-check-driven; no `theory_processed`, no hand-written `on_backtrack`) +
  in-crate `ToyImplTheory` + §4.5 debug-asserts (`!has_pending_propagation()` before decide).
**PROCESS WIN — differential fuzz caught a real spurious-UNSAT (1/10000):** the driver recorded theory
propagations as opaque `Reason::TheoryLemma`, which `analyze` treats as a LEAF (like a decision) → over-strong
learned clause → spurious UNSAT. Fix = materialise the propagation reason as a real clause via
`add_theory_reason_clause` (`Reason::Propagation`) so 1-UIP resolves it (the legacy approach). **Lazy
`TheoryLemma` expansion inside `analyze` is the one DEFERRED §4.3 refinement** (TheoryLemma still carries the
asserting lit = placeholder-elimination; just not yet walked by analyze). Post-fix: 30k differential vs brute
force, 0 unsound; oxiz-sat 616 / oxiz-solver 526 / oxiz-theories 1172 green; Phase-0 soundness regressions pinned.
Gate `oxiz-sat/tests/hooks_diff_fuzz.rs` (30k, brute-force + model-validated).

**PHASE 2 — owning conversion + opt-in hooks driver LANDED & SOUNDNESS-VALIDATED** (branch 0.2.4-redesign; AD1
bumped `02388a1`). Three commits:
- `4513bf3` **owning `TheoryManager`** — `TheoryManager<'a>` (borrowed) → owns euf/arith/bv/statistics + the 5
  read-only maps + `manager: Arc<TermManager>`. `Solver::check` moves state IN per MBQI iteration via
  `take_theory_manager` (O(1) `mem::take`s — maps are read-only during a solve) and OUT via
  `restore_theory_manager`/`into_parts`; per-iteration take/restore reproduces the old recreate-each-round
  semantics (scratch reinit, theory persists). **Arc<TermManager> was the RIGHT design-D choice (I'd second-guessed
  it to plain-owned and was WRONG):** `on_assignment`/`final_check` call `self.process_constraint(…, &mgr)` where
  process_constraint is `&mut self` — a plain `&self.manager` borrow conflicts; `Arc::clone(&self.manager)` gives a
  transient handle INDEPENDENT of `&mut self` (the cheap thing the old `&'a TermManager` got free from `Copy`).
  Reclaimed by value via `Arc::try_unwrap` in `into_parts` (no clone ever stored → refcount 1). Behaviour-preserving:
  752 oxiz-solver tests green.
- `0bb9fc7` **`impl TheoryHooks for TheoryManager`** — SAME real state drives BOTH traits. Opt-in behind
  `SolverConfig::use_hooks_driver` (default OFF) + `(set-option :oxiz.use-hooks-driver true)`. 4→6 hook map:
  push_frame=euf/arith/bv.push (one per level — trail fires once per single level-up, no catch-up loop);
  pop_frame=pop + stale-canonical eviction; unassign_hook=drop phase + queue entry (stale frame UNREPRESENTABLE);
  assign_hook=record phase + QUEUE (driver discards its return); final_check=**reuse legacy final_check VERBATIM in
  forced-`TheoryMode::Lazy`** (drains queue via process_constraint + euf/arith/NO battery), convert
  `TheoryCheckResult`→`TheoryStep`. `check()` branches on the toggle (hooks driver CONSUMES tm + hands it back via
  Any-downcast → rebind). `TheoryManager: Send+Sync+'static` verified.
- `e05b34a` `OXIZ_USE_HOOKS=1` env lever for the z3 fuzz.

**SOUNDNESS VALIDATED (verdict-identical, zero spurious UNSAT):** default forced ON → ENTIRE oxiz-solver suite (526
lib + all integration: EUF/LIA/BV/MBQI/combined/z3-compat) verdict-identical to legacy. New
`hooks_driver_differential.rs` (committed): corpus agrees per-instance + no spurious UNSAT. **z3 differential** (z3
4.16.0): hooks-ON vs hooks-OFF identical across 2500 EUF+LIA + 2500 arith (agree/fatal match exactly). ONE
**pre-existing spurious SAT** (oxiz=sat,z3=unsat) in EUF+LIA — reproduces identically at 012b726 (before the
conversion) in BOTH drivers ⇒ upstream EUF+LIA bug, orthogonal to the swap, NOT introduced here.

**COMPLETENESS gate** (user directive 2026-06-13: "soundness 먼저 완벽하게 → 마지막에 completeness도 완벽하게 =
redesign 완료"; user chose "둘 다 순차로: Phase 2b → spurious SAT → step 5"). The hooks path slowed two suites
~100× (clean_mbqi_wiring 10.5s, ground_soundness_regression 14.4s — verdicts CORRECT, just slower ⇒ Unknown risk
under rlimit).
- **Phase 2b DONE** (`818c4ce`, AD1 `5f502e6`). Root cause was NOT dropped propagations (`process_constraint`
  never returns `Propagated`) — it was the hooks `final_check` running the FULL euf/arith/Nelson-Oppen battery at
  EVERY Boolean fixpoint, where the legacy eager path runs it only at full assignment. Fix: split — oxiz-sat
  `TheoryHooks::final_check_complete` (default delegates to `final_check`, so ToyImplTheory unaffected) fired by
  `solve_with_hooks_inner` ONLY when the assignment is total (last gate before Sat); `TheoryManager::final_check` =
  cheap per-fixpoint drain (shared `drain_queue` + `theory_consistency_check` extract), `final_check_complete` =
  drain + battery. Result: 10.5s→0.03s, 14.4s→0.02s; verdict-identical (oxiz-sat 717 / oxiz-solver 752 / z3-diff
  numerically identical to legacy, ZERO spurious UNSAT). **The redesign's own soundness+completeness for the driver
  swap is DONE (verdict-parity + perf-parity).**
- **Pre-existing spurious SAT — DIAGNOSED, fix NOT yet attempted** (soundness-delicate). Minimal repro (QF_UFLIA):
  `f(1)>=5 ∧ f(1)<=5 ∧ f(f(1))>=10 ∧ f(5)<=1` is UNSAT (f(1)=5 ⟹ congruence f(f(1))=f(5) ⟹ f(5)>=10 vs f(5)<=1)
  but oxiz says SAT. Isolated: the bounds force f(1)=5 but that arith-ENTAILED equality is never propagated to EUF
  to fire the nested congruence (explicit `(= (f 1) 5)` → correctly UNSAT). GAP is in `model_based_combination`
  (`theory_manager.rs:708`): it only DETECTS EUF-equal terms with differing arith values → conflict; it never
  PROPAGATES an arith-fixed shared term into EUF as a constant-equality. Detection is tractable (simplex
  `lower`/`upper: Vec<Option<Bound>>` with `Bound.reasons` already stored — a `fixed_value_with_reasons` query is a
  small oxiz-theories addition). The DANGER: the entailed equality `f(1)=5` has TWO reason atoms (the two bounds)
  but `EufSolver::merge(a,b,reason: TermId)` takes ONE reason term — building a correct all-false conflict clause
  from a multi-reason entailed merge is exactly where a mistake flips to the DANGEROUS spurious UNSAT. So this is a
  genuine theory-combination feature (≈ NO-4: arith→EUF entailed-equality propagation), z3-diff-gated, NOT a quick
  patch. This bug exists in BOTH legacy and hooks paths (engine-wide, orthogonal to the redesign).
- THEN **Phase 2 step 5**: flip default ON + DELETE level_stack/processed_count/the four
  `last_conflict_is_stale_bound` guards. NOT done autonomously — production default change + irreversible deletion,
  gated on Phase 2b (done) + the spurious-SAT fix + user sign-off.

NOTE: user authorized cleaning the stale `rebase-merge` dir AFTER completeness is fully nailed (deferred until the
spurious-SAT item resolves).

NOTE: stale `.git/modules/external/oxiz/rebase-merge` dir (orphaned `feat/enable-writer` DRAT-writer rebase, not
active — `git symbolic-ref HEAD`=0.2.4-redesign; harmless, I didn't create it). Baseline (pre-Phase-2): oxiz-solver
526 + the z3 fuzz already had the 1 pre-existing spurious SAT.

**The OWNERSHIP CRUX + the chosen design (D):** `solve_with_hooks` wants `Box<dyn TheoryHooks + 'static + Send +
Sync>` but `TheoryManager<'a>` BORROWS `&'a mut Euf/Arith/Bv` + `&'a TermManager` + `&'a mut Statistics`. The
`&TermManager` is the blocker (only used to pass to `process_constraint`, which reads `manager.get`/`manager.sorts`
+ recurses via `intern_term_deep` → the read closure reaches `BvSolver::bv_ite` in oxiz-theories, ~218 read-only
`&TermManager` sites total). User REJECTED: full-DAG snapshot (heavy), scoped raw pointer (unsafe), generic/`&dyn
TermRead` threading (cascade into oxiz-theories). **User CHOSE design D: `Arc<TermManager>` whole-manager
read-head** — owning manager holds `Arc<TermManager>`, passes `&*arc` (= `&TermManager`) to theory methods → ZERO
cascade; write path (ematch between solves) uses `Arc::get_mut`/`try_unwrap` (refcount 1 once the read-head drops).
KEY DE-RISK: D is LOCALIZED entirely inside `oxiz-solver Solver::check()` via `std::mem::replace` (move
TermManager + euf/arith/bv into an Arc/owning-manager for the solve, `Arc::try_unwrap` + move back after) — NO
change to `Context.terms` ownership or its 30 usages.

**Phase 2 LANDED so far (branch 0.2.4-redesign):**
- `4b57f96` term-arena read-head split (`TermManager.terms`/`SortManager.sorts` → `Arc<Vec<_>>` + `TermReadView` +
  `TermRead` trait + `read_view`/`sorts_arc`). NOTE: this was the FIRST (arena-granularity) approach; design D
  (manager-granularity `Arc<TermManager>`) SUPERSEDES it — `TermReadView`/`TermRead` are currently UNUSED and
  should be removed in a cleanup once D lands (or kept if a finer read-head is wanted). The `Arc<Vec<Term>>`
  arena-wrapping is harmless under D.
- `012b726` `solve_with_hooks<H: TheoryHooks + 'static>(theory: H) -> (SolverResult, H)` — generic, returns the
  CONCRETE theory (via an `Any` supertrait + downcast) so the SMT path can recover its owned euf/arith/bv after a
  solve. The Phase-1 enabler for D's move-out/move-back.
- AD1 superproject bumped (`0969632`/`7b37659`) to track the oxiz redesign + verification submodules.

**Phase 2 REMAINING (the core):** (1) owning `TheoryHooksManager` struct (owns euf/arith/bv/statistics + `Arc<
TermManager>` + cloned maps) + `into_parts`; (2) `impl TheoryHooks for TheoryHooksManager` — the 4-callback→6-hook
mapping (`theory_manager.rs:1538-1741`): `on_new_level`→`push_frame` (single euf/arith/bv.push, drop the `while
level_stack.len()<level+1`), `on_backtrack`→`pop_frame` (keep the stale-canonical eviction `1716-1734`),
`on_assignment` state→`assign_hook` (accumulate, return Ok), per-assign `process_constraint` work + legacy
`final_check`→`final_check` (CONFLICT channel: `terms_to_conflict_clause` already emits FALSE-under-assignment lits
= the `TheoryStep::Conflict{explanation}` shape, NO negation; PROPAGATE: `explanation` = FALSE non-asserting lits,
the Phase-1 driver negates them for `add_theory_reason_clause`); `eval`→conservative `None` (build_model doesn't
use it); (3) the `check()` hooks-path branch (mem::replace dance) + a `use_hooks_driver` config toggle (default
OFF); (4) VALIDATE new path: z3 differential fatal=0 + old-vs-new verdict identity + adsmt-cli; (5) flip default +
DELETE `level_stack`(`52`,init`490`) + `processed_count`(`54`,`1708`) + the FOUR `last_conflict_is_stale_bound`
guards (`616`/`1092`/`1500`/`1654`) — each a separate commit; KEEP `verify_clean_unsat` as a CI backstop.
RISKIEST = step (2) the hook mapping (eager-vs-final-check: the legacy default is `TheoryMode::Eager` per-assign;
Phase-1 driver is final-check-driven → accumulate+drain in final_check, SOUND but less eager; if z3-diff shows
perf/`Unknown` divergence, thread the deferred eager `assign_hook` return through `solve_with_hooks_inner`
[currently dropped at `trail.rs` `let _ = t.assign_hook(...)`] as Phase 2b).
