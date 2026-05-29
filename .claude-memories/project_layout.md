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

**Crates** (Cargo workspace, edition 2024, resolver 3, triple-licensed
BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later as of v0.18):
- `adsmt-core` — HOL+HKT kernel, 12 inference rules. TCB heart.
- `adsmt-cert` — S-expression certificate format + Lean4/Alethe emit +
  classical-axiom marker layer (mid-blocks, pattern markers,
  StepPattern enum with xor/at_most_one/exactly_one helpers)
- `adsmt-theory` — Theory trait + polite combination + UF/arith/arrays/datatypes
- `adsmt-class` — Type-class layer (T_class) + dictionary passing
- `adsmt-quant` — Quantifier handling (Miller E-matching, prenex,
  Tier 3 bounded enumeration)
- `adsmt-abduce` — Abductive engine (SLD chaining with Horn rules,
  minimize, rank, workflow)
- `adsmt-engine` — DPLL(T) main loop (placeholder)
- `adsmt-parser` — SMT-LIB S-expression + lu-kb parsing (via
  `lu_common::kb` bridge)
- `adsmt-heuristic-checker` — per-user-crate validator for
  classical-axiom heuristic extensions; embeds the adsmt-minimum
  heuristic table (lu-kb source) + 8-layer offline safeguard
- `adsmt-heuristic-checker-macros` — proc-macro entry points
  (`adsmt_heuristics!`, `import_adsmt_heuristics!`,
  `#[derive_heuristics]`)
- `adsmt-lints` — rlib + cdylib for offline-first lints
  (`adsmt_dead_heuristic_pattern` at Warn). nightly-gated
  `dylint-plugin` feature lifts to a real cargo-dylint plugin
- `adsmt-cli` — `lu-smt` binary
- `adsmt-ffi` — C ABI for Lean4/Python/WASM

**External**:
- `external/logicutils/` — git submodule, branch `v0.x-smt`. Tracks
  upstream v0.2.0 commit `39ffc4b` as starting point; SMT-specific
  AST extensions (kind, fundep, overlap) live here. v0.18.0 ships
  the optional `k12` feature (KangarooTwelve-256 + customization-
  string domain separation) in `lu-common` and the new
  `logicutils-translator-to-oxiz-sat` subcrate (deterministic +
  injective lu-kb → CNF translator for adsmt-side minimum-table
  validation).
- **OxiZ** (https://github.com/cool-japan/oxiz, Apache 2.0) —
  cargo dependency from v0.11 onward (Path A+B, see
  `oxiz_relationship.md`). Pure-Rust Z3 reimplementation; adsmt's
  identity is now "abductive + Lean4 layer on top of OxiZ".

**Out-of-tree adsmt-contrib workspace** (`~/adsmt-contrib/`,
separate git repo):
- `adsmt-emit-rocq` — Rocq backend (Ltac2 only; Ltac1 excluded).
  Mirrors `adsmt-cert::lean_emit` shape exactly.
- `adsmt-emit-isabelle` — Isabelle/HOL backend via Isar.
- Both consume `adsmt_cert::prover_emit::common` for the shared
  semantic anchors (Bool→Prop, classical-axiom import family
  enum, etc.).

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
