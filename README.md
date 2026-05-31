# adsmt

**Abductive-deductive HOL+HKT SMT solver, built on OxiZ + a
Lean4-first reflection layer.**

| What | Where |
|---|---|
| Project version | `1.0.0-rc.2` (testing channel) |
| License | BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (triple) |
| Crate roster | 14 `adsmt-*` + 12 absorbed `lu-*` + `adsmt-meta` umbrella |
| ITP targets | Lean4 (in-tree reference), Rocq + Isabelle (out-of-tree via `~/adsmt-contrib/`) |
| SAT backend | `oxiz-sat` (Path A+B default), `cadical` (feature flag), built-in CDCL fallback |
| Engine | DPLL(T) loop with two-watched-literals CDCL, VSIDS, Luby restarts, LBD-aware learnt-clause retention |

## What this is

adsmt is an SMT solver with three differentiating attributes:

1. **Abductive engine** — when ground reasoning gets stuck,
   adsmt's abductive layer (`adsmt-abduce`) finds minimal
   hypothesis sets that would discharge the goal. Tier-4
   escalation surfaces these as `SatResult::Abductive`
   candidates so caller tooling (`smt_abduce` in the Lean4
   tactic harness, the LSP code-action menu, …) can render
   them as `sorry`-shaped holes.

2. **HOL + HKT kernel** — `adsmt-core` ships a higher-order
   logic kernel with higher-kinded types and 12 inference
   rules. The certificate format (`adsmt-cert`) records every
   kernel rule application, theory witness, and abductive
   marker so downstream consumers (Lean4 / Rocq / Isabelle
   reflection) can re-verify under their own kernel.

3. **Pure-Rust solver layer via OxiZ.** adsmt delegates the
   SAT loop and the classical SMT theory stack to
   [OxiZ](https://github.com/cool-japan/oxiz) (a Pure-Rust
   Z3 reimplementation with 100% logic parity), and contributes
   abductive + ITP-reflection-specific capability on top. The
   relationship is **bidirectional embed** per `21E.1
   option 5`: adsmt stays a separate project; specific code
   surfaces (`oxiz-contrib-abduction`, future binding paths)
   flow upstream as Apache-2 contributions.

## Workspace topology (v1.0.0-rc.2)

```
~/AD1/
├── adsmt-core/                    HOL+HKT kernel, 12 inference rules (TCB)
├── adsmt-cert/                    S-expr cert + Lean4 reflection + classical-axiom markers
├── adsmt-theory/                  Theory trait + UF/LIA/LRA/BV/Arrays/Datatypes/Polite
│                                  + EgraphTheory wrapper
├── adsmt-class/                   T_class + dictionary passing
├── adsmt-quant/                   Miller E-matching, prenex, Tier-3 enumeration,
│                                  learn_triggers, EUF-tracked EGraph
├── adsmt-abduce/                  SLD chain + minimize + rank + workflow
├── adsmt-engine/                  DPLL(T) + bool_solver + CDCL + bv_blast
├── adsmt-parser/                  SMT-LIB v2 + lu-kb parser
├── adsmt-heuristic-checker/       8-layer offline safeguard for breaking-versions
├── adsmt-heuristic-checker-macros/ Inert proc-macros + breaking_changes_semver
├── adsmt-lints/                   Runtime audit library (JSON for editor consumption)
├── adsmt-cli/                     `lu-smt` binary, including --audit-json
├── adsmt-ffi/                     C ABI (frozen surface; see include/adsmt.h)
├── adsmt-lsp/                     tower-lsp server (6 capabilities)
├── adsmt-meta/                    Umbrella crate for distro packaging (Arch/Debian/…)
│
├── lu-common/                     lu-kb AST + K12-256 hash + migration chain
│                                  (absorbed RC1.4.A — see ABSORPTION_PLAN.md)
├── freshcheck/  stamp/            lu-* CLI binaries
├── lu-match/    lu-expand/        ↓
├── lu-query/    lu-rule/          ↓
├── lu-queue/    lu-par/           ↓
├── lu-deps/     lu-multi/         ↓
├── logicutils-translator-to-oxiz-sat/  Deterministic lu-kb → CNF translator
│
├── external/oxiz/                 OxiZ submodule (Path A+B fork)
├── contributions/oxiz/            Submodules for Apache-2 OxiZ contributions:
│   ├── abduction/                 oxiz-contrib-abduction (newsniper-org)
│   └── bindings/                  oxiz-binding-* (frozen until leo4 v1.0)
├── tooling/vscode-extension/      VS Code extension + LSP client
└── state/                         {adsmt-frozen, logicutils-frozen, integrated}/
                                   Segregated pre-merge state subtrees per RC1.4
```

Out-of-tree:
- `~/adsmt-contrib/` — Rocq + Isabelle emit backends, mirrors
  the in-tree Lean4 reference via `adsmt-cert::prover_emit::common`
  anchors (lockstep policy in `prover_emit_policy.md`).
- `~/leo4/` — user's dual-ITP binding library (OxiLean + Lean4
  through a single API); a v1.0 release here thaws the
  `contributions/oxiz/bindings/` freeze.

## Quick start

```bash
# Build the workspace
cargo build --workspace

# Run the CLI on an SMT-LIB script
cargo run -p adsmt-cli --release -- examples/qf_uf.smt2

# Start the LSP server (for editor integration)
cargo run -p adsmt-lsp --release

# Run benchmarks (criterion HTML reports under target/criterion/)
cargo bench -p adsmt-engine --bench solver_smoke
cargo bench -p adsmt-engine --bench cdcl_smoke

# Build the umbrella crate with everything enabled
cargo build -p adsmt-meta --features full

# Library-only build (skips lu-* CLIs)
cargo build -p adsmt-meta --no-default-features --features no-cli
```

## Editor integration

- **VS Code**: install the extension under `tooling/vscode-extension/`
  (run `npm install && npm run compile` then F5 from VS Code).
  The extension spawns `adsmt-lsp` via stdin/stdout LSP.
- **Other editors** (neovim, emacs, helix, …): point the
  client at the `adsmt-lsp` binary; the extension's
  `audit.ts` editor-agnostic layer is reusable as a
  TypeScript reference for other LSP-client environments.

LSP capabilities (`memory/lsp_roadmap.md` §"Phase 2 sign-off"):
- `textDocument/publishDiagnostics` (parser + audit
  diagnostics)
- `textDocument/definition` (within-doc symbol resolution)
- `textDocument/hover` (BV literal annotation + declaration
  preview)
- `textDocument/completion` (39 static items: SMT-LIB
  commands, theory names, classical-axiom families, lu-kb
  keywords)
- `workspace/symbol` (case-insensitive substring across open
  docs)
- `textDocument/codeAction` (kb-file migration placeholder
  for v0.x → v1.x)

## License

Triple-licensed at the consumer's choice:
- [BSD-2-Clause](LICENSE-BSD.txt)
- [Apache-2.0](LICENSE-APACHE.txt)
- [LGPL-2.1-or-later](LICENSE-LGPL.txt)

The triple matches what adsmt-side contributors have always
agreed on. OxiZ-side contributions (under
`contributions/oxiz/*` or upstreamed to `cool-japan/oxiz`)
flow under Apache-2 alone, matching OxiZ upstream.

The LGPL-2.1-or-later option carries one nuance worth flagging
for embedders: per the
[LGPL FAQ](https://www.gnu.org/licenses/lgpl-2.1.html), the
copyleft scope only triggers when the user modifies an
LGPL-licensed component itself; using it unmodified leaves the
consumer's code under its own license. Rust source-distribution
patterns satisfy LGPL §6 automatically (any sibling crate can
swap the dep version via `cargo update` / `[patch.crates-io]`).

## Versioning + channels

adsmt uses a Debian-style channel model:

| Channel | Branch | Purpose |
|---|---|---|
| `unstable` (sid) | `main` | Active development; new commits land here first |
| `testing` | `testing` | Stabilisation candidates promoted from `main` |
| `stable` | `v1.0.0` (tag) | Released versions (the v1.0.0 tag is the first cut) |

The 8-layer offline safeguard (`adsmt-heuristic-checker`)
tracks every breaking-version bump under semver from v1.0.0
onward — see `adsmt-ffi/ABI_POLICY.md`,
`adsmt-parser/DIALECT_POLICY.md`, `adsmt-cert/CERT_POLICY.md`
for the three frozen authority surfaces.

`#[adsmt_heuristic_checker_macros::breaking_changes_semver("1.0.0")]`
is the first live attribute, stamped on `adsmt-ffi`,
`adsmt-cert`, and `adsmt-parser`'s `lib.rs` at RC1.3.

## Related projects

- **OxiZ** [cool-japan/oxiz](https://github.com/cool-japan/oxiz)
  — Pure-Rust Z3 reimplementation; adsmt's SAT/theory
  delegation target.
- **leo4** [Honey-Be/leo4](https://github.com/Honey-Be/leo4)
  — user's dual-ITP (OxiLean + Lean4) binding library;
  governs the binding-freeze policy in
  `contributions/oxiz/bindings/`.
- **logicutils** (absorbed at RC1.4.A from the v0.x-smt
  branch; the original repo continues for non-SMT
  use cases — adsmt's absorbed copy is the canonical
  source going forward).

## Contributing + governance

This repo's `main` branch is the development channel. Pull
requests are reviewed against the audit guards documented
under each surface-policy markdown. Open-ended discussion
happens in `memory/` markdown files (project-internal); the
broader design archive lives in `.claude-conversations/`.

For OxiZ-side contributions
(`contributions/oxiz/abduction/`, `contributions/oxiz/bindings/`)
follow the upstream repo's contribution guide; for
out-of-tree adsmt backends (`~/adsmt-contrib/`) follow that
repo's README.

## Audit + verification

Top-level audit documents:
- [`ABSORPTION_PLAN.md`](ABSORPTION_PLAN.md) — RC1.4.A
  logicutils absorption execution record.
- [`CONTRIBUTIONS_AUDIT.md`](CONTRIBUTIONS_AUDIT.md) —
  RC2.7 audit of `contributions/*` + `~/adsmt-contrib`.
- [`DOC_AUDIT.md`](DOC_AUDIT.md) — RC2.4 + RC2.8 cargo doc
  surface audit.
- [`PUBLISH_AUDIT.md`](PUBLISH_AUDIT.md) — RC2.2
  cargo-publish dry-run audit and the v1.0.0 cut prerequisite
  list.

Memory pointers (project-internal context):
- `project_layout.md` — crate responsibilities
- `project_cycle_versioning.md` — cycle history
- `oxiz_relationship.md` — Path A+B + P5 outcome
- `logicutils_version_rule.md` — absorption history
- `lsp_roadmap.md` — phase 1/2/3 sign-offs
- `prover_emit_policy.md` — Lean/Rocq/Isabelle lockstep
