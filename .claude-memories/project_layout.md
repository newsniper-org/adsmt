---
name: adsmt project layout
description: Workspace topology, crate responsibilities, and the logicutils submodule
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
`adsmt` is a Lean4-native SMT solver built on abductive-deductive
logic, designed as a split sibling of logicutils. Workspace at
`/home/ybi/AD1/` (project name is `adsmt`, not the directory name
`AD1`).

**Crates** (Cargo workspace, edition 2024, resolver 3, BSD-2-Clause):
- `adsmt-core` — HOL+HKT kernel, 12 inference rules. TCB heart.
- `adsmt-cert` — S-expression certificate format + Lean4/Alethe emit
- `adsmt-theory` — Theory trait + polite combination + UF/arith/arrays/datatypes
- `adsmt-class` — Type-class layer (T_class) + dictionary passing
- `adsmt-quant` — Quantifier handling (Miller E-matching, prenex)
- `adsmt-abduce` — Abductive engine (SLD, minimize, rank, workflow)
- `adsmt-engine` — DPLL(T) main loop (placeholder)
- `adsmt-parser` — SMT-LIB S-expression + lu-kb parsing
- `adsmt-cli` — `lu-smt` binary
- `adsmt-ffi` — C ABI for Lean4/Python/WASM

**External**:
- `external/logicutils/` — git submodule, branch `v0.x-smt`. Tracks
  upstream v0.2.0 commit `39ffc4b` as starting point; SMT-specific
  AST extensions (kind, fundep, overlap) live here.

**Why this matters:**
- Design rationale lives in
  `.claude-conversations/2026-05-12-smt-solver-design.md`. Always
  consult that file first when continuing work.
- Submodule writes happen *inside* `external/logicutils/`; remember
  to commit there (not in the parent repo) and update the parent's
  submodule pointer afterward.

**How to apply:**
- Before designing new crates or modifying dependencies, check
  whether the design conversation already settled the question.
- Submodule version bumps follow the rule in
  `logicutils_version_rule.md`.
