---
name: oxiz-nlsat-redesign
description: "DECIDED 2026-06-23 — clean-room redesign of OxiZ's whole nonlinear solver (NIA+NRA) as `oxiz-nl2`: MCSAT-trail spine + monotone-strength explainer ladder, two runtime soundness gates, M0–M7 roadmap. Architecture FINALIZED; design doc next."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**Clean-room redesign of OxiZ's NONLINEAR arithmetic solver — DECIDED 2026-06-23.** Triggered by the [[nlsat_algebraic_reduction_kb]] z3-differential finding: OxiZ's current core solvers — `NlsatSolver` (real, `oxiz-nlsat/src/solver/`) AND `NiaSolver` (integer, `oxiz-nlsat/src/nia.rs`) — are **BROADLY UNSOUND on nonlinear `unsat`** (single-atom false-unsat: NRA deg-2 13%/deg-3 32%/deg-4 16%; NIA 58/400 — `3x²<5`, `x⁴>4` decided spurious `unsat`). Current OxiZ is held SOUND only by BAND-AIDS (`2e86546`: `unsat_is_trustworthy` gates trust the core's unsat ONLY on the linear fragment `total_degree≤1`, with §G/§G-SOS/trichotomy as the sound nonlinear-unsat deciders) — soundness at a COMPLETENESS cost (the ~25% z3-divergences that remain are all verus-safe FALSE_SAT). The real fix is a SOUND nonlinear solver.

**SCOPE (user): NIA+NRA UNIFIED** — the whole nonlinear solver, one shared core; replaces both `NlsatSolver` and `NiaSolver`.

**PATTERN: same playbook as the proven clean-room redesigns** — [[oxiz_mbqi_rewrite]] (clean-MBQI at `~/oxiz-mbqi`, M4-ported) and [[oxiz_sat_core_redesign]]/[[oxiz_redesign_verification_pipeline]] ([선검증→구현→후검증]). Develop+verify in isolation, then M4-port into OxiZ and DELETE the band-aid gates.

## FINALIZED ARCHITECTURE (2026-06-23, design-workflow `weq2sfptc` 7-agent + user calls)
**`oxiz-nl2` = MCSAT-trail spine + a monotone-strength EXPLAINER LADDER.** One frozen model-constructing MCSAT loop over OxiZ's EXISTING `Assignment`/`IntervalSet`/`feasible`/`var_order` substrate (`oxiz-nlsat/src/{assignment,interval_set,var_order}.rs`). `Sat` is witnessed BY CONSTRUCTION (the trail). The soundness seam is exactly **one function `explain` → returns a clause valid over ℝ**; the loop + data structures are frozen at M1 and NEVER rewritten — only the explainer grows (interval → §G/linearization → McCallum/CDCAC covering). This is the ONLY proposal whose single fixed loop spans the whole sound-first→complete arc with no rewrite (rivals: sound-first-IL has a completeness ceiling it can only break by becoming CDCAC; cdcac-complete pays full engine cost up front). IL's lemma library is FOLDED IN as a cheap M2 explainer tier (not a competing engine); CDCAC's covering is realized INSIDE `explain` at M4.

**TWO RUNTIME GATES make FALSE_UNSAT=0 / FALSE_SAT=0 hold from commit 1, regardless of explainer correctness:** **G-SAT** = exact model re-check (every `Sat` carries a point of `BigRational|AlgebraicNumber`, substitute+check sign exactly; fail→Unknown — promotes today's `model_satisfies_atoms` from band-aid to guarantee); **G-UNSAT** = covering re-verification (every `Unsat` carries a covering + infeasible subset, re-verify each cell is genuinely unsat for its tagged atom + cells union to ℝ; fail→Unknown). False verdicts are STRUCTURALLY impossible, so every milestone is independently shippable and completeness only ever LOWERS the Unknown rate.

**z3-DIFFERENTIAL as the day-1 regression spine** (`$CLAUDE_JOB_DIR/tmp/diff_*.py` → `nl_differential` corpus): invariant **FALSE_UNSAT=0** (verus-dangerous, hard gate) + **FALSE_SAT=0**; Unknown-rate tracked per degree/arity, non-gating. z3 4.16.0 + cvc5 1.3.0 local oracles. See [[feedback_z3_differential_for_unsat_trust]].

## MILESTONE ROADMAP (each ships sound; only ADDS decisiveness; loop frozen at M0/M1)
- **M0** — z3-diff gate (seeded `3x²<5`,`x⁴>4`,`x·y>5`,`3x²≥25`,`x²=3` + bounded random gen) + crate skeleton `~/oxiz-nl2`, `Explainer` trait, `Value`/`Model` carrying `AlgebraicNumber` losslessly.
- **M1** — sound MCSAT spine + interval explainer + **§G folded in** (user: "interval + §G 함께, 조금 크게"); rational-only sampling, `explain`=interval-exclusion generalised by "sign constant between rational roots", algebraic bound→`GiveUp`/Unknown; G-SAT live. **Closes every documented single-atom false-unsat (the P0 deliverable).** No new algebraic math.
- **M2** — linearization explainer tier (IL lemma library: sign/zero/monotone/tangent-plane, RATIONAL anchors only) behind `explain`. Closes bulk of "needs one valid lemma" multivariate unsats. Still rational-only, Verus-trivial.
- **M3** — local-search SAT portfolio (critical-move+PAWS, exact witnesses, never-unsat) + build the TWO hard algebraic primitives `sign_at_algebraic` + resultant-encoded algebraic-coord root isolation (fuzzed in isolation vs z3 before wiring). The bug-prone math, quarantined behind G-gates.
- **M4** — model-based McCallum projection → CDCAC cylindrical covering as `UnsatReason`; G-UNSAT covering re-verify ON; nullification→Unknown. **Sound+complete QF_NRA modulo nullification.**
- **M5** — NIA: real-relaxation (real-unsat⟹int-unsat) + integer-prefer sampling + conflict-directed B&B + exact int-infeasibility certs (perfect-square/parity/divisibility) + the **Borralleras Thm 3.1 artificial-bound-core gate** (the precise condition replacing the `total_degree≤1` NIA band-aid).
- **M6** — Verus pre-verification in `oxiz-nl2-verification` (mirror `oxiz-sat-redesign-verification`): loop invariant, covering bookkeeping, interval+linearization tier S1 validity, G-SAT predicate, NIA bound-core gate. Runnable from M2.
- **M7** — **Lazard projection = COMMITTED milestone** (user: not a deferred frontier) — kills nullification-Unknown; + projective-delineability, conflict minimization, "More is Less" cheap resultants.

**Band-aid deletion (gated on the differential, NEVER a date):** `model_satisfies_atoms`→defense-in-depth at M1 (kept). `unsat_is_trustworthy=total_degree≤1` → delete **NRA gate at M4**, **NIA gate at M5** (after bound-core lands), each only when differential is FALSE_UNSAT=0 on the full corpus. §G/§G-SOS/trichotomy → **KEPT PERMANENTLY as Layer-0 fast pre-deciders** (absorbed, not deleted). `NlsatSolver`+`NiaSolver` → deleted after `oxiz-nl2` passes corpus+differential (same as `oxiz-solver/src/mbqi/` #262).

## REUSE vs BUILD
**Reuse as-is:** `AlgebraicNumber{new,signum,compare,add,mul,negate,refine}` (`oxiz-math/src/algebraic/number.rs`); `root_isolation::isolate_roots` + Sturm `root_counting`; projection toolkit `resultant`/`discriminant`/`subresultant_prs`/`leading_coeff_wrt`/`eval_at`/`square_free`/`primitive`; `IntervalSet{intersect,complement,sample,is_reals,from_constraint}` + the whole trail substrate; §G/§G-SOS `discriminant.rs` + `TermPolyTranslator`. **Build exactly TWO primitives, both at M3, both behind the G-gates** (all 3 studies name these as THE soundness gaps): (1) `sign_at_algebraic(p,partial_model)→Sign` — exact multivariate sign at a possibly-algebraic point (the existing `advanced_ops::sign_at` is a SYNTACTIC `Var→sign` heuristic, MUST NOT be used for verdicts); (2) real-root isolation with an algebraic sample coord via resultant-encoding (`res_{x_j}(p,m_j)` keeps coeffs over ℚ). M1+M2 need NEITHER (rational-only until the McCallum tier).

## USER'S 4 FINAL DESIGN CALLS (2026-06-23)
1. **Repo topology** = separate `~/oxiz-nl2` + `~/oxiz-nl2-verification` (clean-room precedent), M4-ported into `external/oxiz/oxiz-nl2/`.
2. **M1 scope** = interval + §G TOGETHER (slightly larger first milestone, closes more immediately).
3. **IL/linearization tier** = PERMANENT (kept as a fast pre-explainer even after M4's McCallum subsumes it on QF_NRA).
4. **Nullification** = Lazard is a COMMITTED milestone (M7), not an indefinite frontier deferral.

**2 tactical defaults to set in the design doc:** budget topology (per-tier vs global step/node budgets — leaning PER-TIER: LS time-box ⟂ projection step-cap ⟂ NIA branch-depth); NIA artificial-bound initial width + widening schedule (Borralleras bound-core, M5).

## KICKOFF PROCESS (user-specified) — current position
(1) memory+mirror+commit [DONE] → (2) architecture discussion [DONE] → (3) memory+mirror+commit [DONE] → (4) design doc [DONE — `~/oxiz-nl2/DESIGN.md`] → (5) implementation **IN PROGRESS**. Full design-workflow synthesis at `~/research-library/nonlinear-solvers/DESIGN-WORKFLOW-SYNTHESIS.md` (1214 lines). Papers: [[research-library-nonlinear-solvers]].

## IMPLEMENTATION PROGRESS (`~/oxiz-nl2`, standalone git repo, UNPUSHED — separate from AD1/external/oxiz)
- **M0 DONE** (`c97e85c`): crate skeleton (path-dep on vendored `oxiz-math`); `Value`/`Model` (lossless `AlgebraicNumber`) + **G-SAT** `Model::checks`; `Explainer` seam; z3-differential gate (SMT-LIB serialiser + z3 oracle + FALSE_UNSAT/FALSE_SAT classifier + seeded shapes + deterministic LCG random gen).
- **M1 DONE** (`ba2bb4a`) — the P0-closing milestone: frozen var-by-var model-construction spine (rational sampling + backtracking) over `oxiz-nlsat`'s `IntervalSet` substrate; Layer-0 §G/§G-SOS folded in (`oxiz_nlsat::discriminant`); integer-sort = integers-only + integrality guard. Verdicts: Sat only via exact G-SAT; Unsat only via §G or single-var representative-point emptiness; else Unknown. **Full z3-differential: 1007 cases, FALSE_UNSAT=0 / FALSE_SAT=0, 809 agree, 198 sound Unknown.** 30 unit tests, clippy clean.
- **TWO substrate soundness BUGS found by the differential during M1** (latent in the OLD `oxiz-nlsat` — extra evidence for the redesign; oxiz-nl2 now NEVER trusts them for a verdict): (a) `cad::SturmSequence::count_roots()` reports `-5x⁴+1` (NEGATIVE leading coeff) as **rootless** though it has 2 real roots → would cause false-unsat; oxiz-nl2 instead decides "all real roots rational" by **exact deflation** (synthetic division), never a library root count. (b) `IntervalSet::intersect` **drops the point `{0}`** intersected against `(-∞,0)∪[0,∞)` at the boundary → would cause false-unsat; oxiz-nl2 decides single-var unsat by **representative-point evaluation** over sign-cells, never `intersect`. (If the user fixes these in oxiz-nlsat directly, they are also real QF_NRA soundness bugs in the current solver.)
- **NEXT = M2** (linearization/IL explainer tier, rational anchors) per [[oxiz-nlsat-redesign]] roadmap; then M3 (LS + 2 algebraic primitives), M4 (McCallum/CDCAC), M5 (NIA), M6 (Verus), M7 (Lazard). Substrate-bug avoidance is a standing M-rule. The 198 Unknowns are the M2–M4 completeness frontier.
