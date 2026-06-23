---
name: oxiz-nlsat-redesign
description: "DECIDED 2026-06-23 — clean-room redesign of OxiZ's whole nonlinear solver (NIA+NRA, NlsatSolver+NiaSolver) in a separate repo, because a z3-differential proved both core solvers broadly unsound on nonlinear unsat. Kickoff staged; not started."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**Clean-room redesign of OxiZ's NONLINEAR arithmetic solver — DECIDED 2026-06-23 (user proposal).** Triggered by the [[nlsat_algebraic_reduction_kb]] z3-differential finding: OxiZ's current core solvers — `NlsatSolver` (real, `oxiz-nlsat/src/solver/`) AND `NiaSolver` (integer, `oxiz-nlsat/src/nia.rs`) — are **BROADLY UNSOUND on nonlinear `unsat`** (single-atom false-unsat: NRA deg-2 13%/deg-3 32%/deg-4 16%; NIA 58/400 — `3x²<5`, `x⁴>4` decided spurious `unsat`). This is not a small bug; it is not worth incrementally patching. The current OxiZ is held SOUND only by BAND-AIDS (`2e86546`: the `unsat_is_trustworthy` gates now trust the core's unsat ONLY on the linear fragment, with §G/§G-SOS/trichotomy as the sound nonlinear-unsat deciders) — which restores soundness at a COMPLETENESS cost (the ~25% z3-divergences that remain are all FALSE_SAT = "a sound nlsat would decide these"). The real fix is a SOUND nonlinear solver.

**SCOPE (user, 2026-06-23): NIA+NRA UNIFIED** — the whole nonlinear solver. Real CAD (`NlsatSolver`) and integer-nonlinear (`NiaSolver`) share a CAD core, so design them together. Replaces both.

**PATTERN: same playbook as the proven clean-room redesigns** — [[oxiz_mbqi_rewrite]] (clean-MBQI dev'd at `~/oxiz-mbqi`, M4-ported) and [[oxiz_sat_core_redesign]] / [[oxiz_redesign_verification_pipeline]] (SAT core, [선검증→구현→후검증] = Verus pre-verification → implement → z3-diff post-verification). Separate external repo (`~/oxiz-nlsat-redesign` or similar), develop+verify in isolation, then M4-port into OxiZ and DELETE the band-aid gates (trust the new sound solver).

**THE VERIFICATION SPINE: z3-differential as a day-1 soundness GATE.** The harness that found the bug (`$CLAUDE_JOB_DIR/tmp/diff_*.py` — generates randomized QF_NRA/QF_NIA nonlinear formulas, cross-checks OxiZ vs z3, classifies FALSE_UNSAT vs FALSE_SAT) becomes the redesign's regression spine. Invariant enforced from the start: **FALSE_UNSAT = 0** (the verus-dangerous direction); FALSE_SAT (incompleteness) shrinks as completeness improves. z3 4.16.0 + cvc5 1.3.0 are installed locally as oracles.

**KICKOFF PROCESS (user-specified, 2026-06-23):** (1) memory update + `just mirror-memory` + commit [DONE this step] → (2) architecture/algorithm/strategy discussion → (3) memory update + mirror + commit → (4) write design doc → (5) full implementation. Currently at step 2 (architecture discussion) next.

**Design questions for step 2 (architecture):** which CAD algorithm (full Collins CAD vs the lazy/conflict-driven nlsat of Jovanović–de Moura vs a model-constructing approach); exact real-algebraic-number representation (reuse `oxiz_math::algebraic::AlgebraicNumber` / the reduction-KB's Sturm machinery, or fresh); the SAT-direction model-construction + verification (so `Sat` carries a checkable model, unlike today); integer-feasibility for NIA (CAD over ℝ + an integer search, or a dedicated nonlinear-integer method); how it plugs the `TheoryHooks`/`dispatch_nl_solver` seam; and whether to keep §G/§G-SOS/trichotomy as fast pre-deciders in front of the full CAD.
