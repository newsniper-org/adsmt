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
- `adsmt-theory` — Theory trait + polite combination + UF/arith/arrays/datatypes/BV/(v0.23) EgraphTheory wrapper. The EgraphTheory module wraps `adsmt_quant::egraph::EGraph` and is registered alongside UF when EUF congruence cascade visibility is required by peer theories via `derive_equalities`.
- `adsmt-class` — Type-class layer (T_class) + dictionary passing
- `adsmt-quant` — Quantifier handling (Miller E-matching, prenex,
  Tier 3 bounded enumeration). v0.19 A.3 partial: `trigger::learn_triggers`
  greedy depth-ordered cover. v0.21 A.2 stages 1+2: new `egraph`
  module — hash-consed + union-find `EGraph` with congruence-closure
  cascade (upward merging on `merge`); stages 3 (incremental
  E-matching loop) and 4 (push/pop scope) pending.
- `adsmt-abduce` — Abductive engine (SLD chaining with Horn rules,
  minimize, rank, workflow)
- `adsmt-engine` — DPLL(T) main loop + Boolean engine (`bool_solver`),
  CNF flattener (`cnf`), v0.19 C.1 **BV bit-blasting module
  `bv_blast`** lowering BV equalities/binops into CNF over fresh
  `__bvb_<var>_<idx>` atoms with `__bva_<n>` Tseitin auxiliaries.
  v0.19 B.2: `dpllt::run_once` now eager-conflict short-circuits
  on the first `AssertResult::Conflict` from any theory. v0.19
  D.1: Tier 4 abductive escalation runs `minimize` + `rank_candidates`
  on emitted `quant-tier4` candidates. v0.21 B.1: full CDCL in
  the new `cdcl` module — trail + 1-UIP + learnt clauses +
  non-chronological backjump + Luby restart wrapper + VSIDS +
  clause deletion + activity-based retention + LBD glue
  protection (≤ 6) + phase saving + Sat-side model carry-out
  via `CdclOutcome::Sat { model }`. Wired as the built-in SAT
  fallback in `Solver::check_ground`. Two-watched literals +
  LBD-based restart triggers queued for v0.23. v0.21 C.1:
  `bv_blast` extended with ripple-carry `bvadd`/`bvsub` and
  shift-and-add `bvmul`.
- `adsmt-parser` — SMT-LIB S-expression + lu-kb parsing (via
  `lu_common::kb` bridge)
- `adsmt-heuristic-checker` — per-user-crate validator for
  classical-axiom heuristic extensions; embeds the adsmt-minimum
  heuristic table (lu-kb source) + 8-layer offline safeguard
- `adsmt-heuristic-checker-macros` — proc-macro entry points
  (`adsmt_heuristics!`, `import_adsmt_heuristics!`,
  `#[derive_heuristics]`)
- `adsmt-lints` — **runtime audit library** (rlib only since
  v0.18 F.4-redo; the cargo-dylint plugin path was scrapped
  in favour of runtime audits because cert is a runtime
  object). Exposes `dead_pattern_audit(&Certificate)` +
  `audit_to_json` (versioned JSON schema for IDE
  consumption).
- `adsmt-cli` — `lu-smt` binary. v0.19 added `--audit-json`
  flag emitting the dead-pattern audit JSON to stderr after
  each `(check-sat)`.
- `adsmt-ffi` — C ABI for Lean4/Python/WASM. v0.19 froze the
  surface header (`include/adsmt.h`) + ABI policy
  (`ABI_POLICY.md`). v0.x → no guarantees; v1.0+ → full
  semver-bound.

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
  Mirrors `adsmt-cert::lean_emit` shape exactly. v0.19 K-full:
  Trans/EqMp/Deduct/Abs/Beta/Inst/InstType all emit real proof
  terms.
- `adsmt-emit-isabelle` — Isabelle/HOL backend via Isar. Same
  K-full coverage as Rocq.
- Both consume `adsmt_cert::prover_emit::common` for the shared
  semantic anchors (Bool→Prop, classical-axiom import family
  enum, scan-arm axiom keyword tables, etc.).

**Tooling** (`tooling/`):
- `tooling/vscode-extension/` — VS Code extension. v0.19 F.1
  shipped audit-JSON consumer; v0.25 EXT.1 split it into
  `src/audit.ts` (editor-agnostic JSON parsing) and
  `src/extension.ts` (VSCode-specific commands + LSP client
  via `vscode-languageclient`). Talks to the v0.25 `adsmt-lsp`
  server binary for live capabilities.
- `adsmt-lsp` (workspace crate, v0.25 25LSP.*) — tower-lsp
  server with 6 capabilities: publishDiagnostics, definition,
  hover, completion, workspace/symbol, codeAction. Spawned
  as a child process by the vscode-extension; usable from
  any LSP client (neovim, emacs, helix).

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
