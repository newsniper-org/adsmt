---
name: research-library-nonlinear-solvers
description: "~/research-library/nonlinear-solvers/ holds 13 nonlinear-SMT-solver papers (2012→2026) + README index, collected to inform the OxiZ nonlinear-solver clean-room redesign. Not committed (3rd-party PDFs)."
metadata: 
  node_type: memory
  type: reference
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

`~/research-library/nonlinear-solvers/` (NOT the `.claude-research-library/` MBQI one — a sibling top-level lib) holds **13 nonlinear-arithmetic SMT-solver papers (2012→2026)** + a `README.md` index, collected 2026-06-23 to inform the [[oxiz_nlsat_redesign]] clean-room nonlinear-solver redesign. 3rd-party PDFs — NOT committed.

Decision-relevant clusters (see the README for the full index + per-paper notes):
- **CDCAC (Conflict-Driven Cylindrical Algebraic Coverings)** — Ábrahám/Davenport/England/Kremer 2020 (arXiv 2003.05633) + 2026 optimisation (2601.14424). The algorithm cvc5/SMT-RAT/Maple use; conflict-driven CAD-for-SAT; the recommended completeness target (the bridge between MCSAT and full CAD).
- **nlsat/MCSAT** — Jovanović–de Moura 2012 FOUNDATIONAL (z3/Yices), + 2024 clauseSMT (2406.02122), 2025 "more is less" explanations (2512.14269), 2025 MCSat-NIA (2503.01627).
- **Incremental linearization** — Cimatti et al 2018 (1801.08723): UF-abstract nonlinear terms + piecewise-linear refinement, SOUND by construction, reduces to LRA+UF (which OxiZ already has soundly) — the candidate low-effort sound-first FOUNDATION (returns Unknown when undecided).
- **NIA** — incomplete-SMT-over-integers 2020 (2008.13601) + the MCSat-NIA + local-search papers.
- **Local search** — 2023 NRA (2311.14249), 2022 integer (2211.10219): fast SAT-side model-finding (checkable model, no unsat).
- **CAD theory / surveys** — projective delineability 2024 (2411.13300), real-QE/CAD survey 2024 (2407.19781), interpolation/model-checking 2021 (2106.04340).

Used by the design-workflow (study→propose→critique→synthesize) that produced the architecture recommendation for [[oxiz_nlsat_redesign]] — see that memory for the chosen design.
