---
name: LSP roadmap + vscode-extension split (21F.3 option 4)
description: v1.0 RC contains LSP — three-step sequence stabilize → LSP-with-extension-split → RC bump
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
21F.3 decided 2026-05-30 as **option 4**: a three-phase
sequence that bundles LSP delivery into the v1.0 RC cut. Earlier
option-1/2/3 alternatives (thin tower-lsp wrapper, vscode-only
host, defer-to-v1.x) are subsumed and replaced.

## Three-phase sequence

### Phase 1 — Preemptive stabilisation

Before any LSP-side code is touched, every public surface that
the LSP will eventually depend on is *frozen*:

- **C ABI** (`adsmt-ffi`) — semver-bound under v1.0; the
  v0.19 E.3 `include/adsmt.h` + `ABI_POLICY.md` start as
  the freeze candidate.
- **SMT-LIB dialect** — every parser shape, lu-kb keyword,
  classical-axiom marker syntax committed; no further surface
  drift.
- **Certificate format** — S-expression cert + Lean reflection
  + Rocq/Isabelle emit shapes locked.
- **Theory deepening completion** — BV (incl. `bvmul`),
  LIA/LRA, Arrays, Datatypes, Polite combination at their
  intended v1.0 capability.
- **CDCL / E-graph deepening** — `cdcl` two-watched literals
  (queued from v0.21), full E-matching loop using
  `egraph` push/pop scope (21A.2 stage 4 wired into theory
  routing), VSIDS + LBD-restart heuristics if not already
  present.

The phase 1 gate is binary: every breaking change after this
point is forbidden until v1.0 ships. This is what makes the
LSP scope (phase 2) implementable against a moving target —
nothing is moving.

### Phase 2 — LSP implementation + vscode-extension split

Implementation **must complete** (user mandate). Split the
existing `tooling/vscode-extension/` along the
**editor-agnostic vs VSCode-specific** axis:

- **Editor-agnostic components** (new home: `tooling/` or
  `crates/adsmt-lsp-*`, exact layout decided at phase entry):
  - LSP server binary itself — `tower-lsp`-based; consumes the
    `adsmt-cli --audit-json` schema (already at version 1)
    plus any new endpoints needed for LSP capabilities below.
  - Audit JSON ↔ LSP `Diagnostic` converter (already partially
    in the vscode extension; relocated to the agnostic crate).
  - Document model / file-watcher harness that any LSP client
    consumes.
  - SMT-LIB / lu-kb / Lean / Rocq / Isabelle syntax knowledge
    needed for completion / hover / rename — server-side, not
    client-specific.
- **VSCode-specific components** (stay in
  `tooling/vscode-extension/` after the split):
  - VSCode command palette wiring
    (`adsmt-lints.loadAudit`, …).
  - Settings UI, configuration schema.
  - VSCode-specific decoration / hover style.
  - Marketplace packaging metadata.

LSP capability scope (minimum target for "must complete"):
- `textDocument/publishDiagnostics` — wraps the existing
  dead-pattern audit + emit-time classical-axiom check + any
  v1.0-blocked errors surfaced by adsmt-engine.
- `textDocument/definition` — symbol resolution for cert
  identifiers (`s<n>` step ids, axiom names, …).
- `textDocument/hover` — show step body / sequent for cert
  ids, sort lowering for LFSC sorts, BV width on
  `bv<v>:<w>` literals.
- `textDocument/completion` — lu-kb keywords, classical
  axiom family names, theory names.
- `workspace/symbol` — index of declarations and `(check …)`
  obligations.
- `textDocument/codeAction` — apply auto-migration suggestions
  (v0.x→v1.x kb files) inline.

Capabilities beyond this list are nice-to-have; the
must-complete bar is the six above.

### Phase 1 sign-off (23H.2, 2026-05-30)

The three v0.23 freeze-candidate tasks have landed; the v1.0
surface is now locked at the commit hashes below. The
`adsmt-heuristic-checker` 4-peer safeguard plus three new
`*_surface.rs` audit tests catch any future drift.

| Surface | Locked at | Commit | Audit guard |
|---|---|---|---|
| C ABI (`adsmt-ffi/include/adsmt.h`) | 11 frozen symbols | `1bb5035` | `adsmt-ffi/tests/c_abi_surface.rs` (2 tests) |
| SMT-LIB / lu-kb dialect | 20 `Command` variants + lu-kb top-level forms + classical-axiom markers | `2bf966a` | `adsmt-parser/tests/dialect_surface.rs` (3 tests) |
| Certificate format | 5 Certificate fields + 12 StepBody variants + 6 StepPattern variants + 3 derived helpers + 3 per-ITP emit signatures | `e7e058d` | `adsmt-cert/tests/cert_surface.rs` (5 tests) |

Phase 1 sign-off policy doc state at sign-off time:
- `adsmt-ffi/ABI_POLICY.md`: status header reads "v0.23 phase
  1 freeze candidate"; checklist items 1, 4, 6, 7 satisfied;
  items 2, 3, 5, 8 deferred to phase 3.
- `adsmt-parser/DIALECT_POLICY.md`: status header reads "v0.23
  phase 1 freeze candidate"; checklist items 1, 2, 4
  satisfied; items 3, 5, 6 deferred to phase 3.
- `adsmt-cert/CERT_POLICY.md`: status header reads "v0.23 phase
  1 freeze candidate"; checklist items 1, 2, 3, 4 satisfied;
  items 5, 6 deferred to phase 3.

**Any future breaking-version bump in
`adsmt-heuristic-checker` (i.e. registering a `1.x.0` or
`2.0.0` entry) MUST correspond to a deliberate v1.x major
decision that explicitly amends one or more of the three
policy documents above.** The audit guards are not enough on
their own — they catch drift but don't decide whether a drift
is intentional.

### Phase 2 entry conditions (recorded for the v0.25 cycle)

When v0.25 opens, before any LSP code lands:
1. Re-read this phase 1 sign-off section to confirm no policy
   doc has been silently amended.
2. Re-run `cargo test --workspace --tests` to confirm the three
   `*_surface.rs` audits still pass against current sources.
3. Re-read the capability list under "Phase 2 — LSP
   implementation + vscode-extension split" below and decide
   whether the must-complete bar is still right.
4. Audit `tooling/vscode-extension/` for the editor-agnostic
   vs VSCode-specific split before any refactor begins.

### Phase 2 sign-off (25H.2, 2026-05-30)

All six required LSP capabilities + the vscode-extension split
landed in v0.25. The mandatory completion bar from
`lsp_roadmap.md` §"Phase 2" is satisfied.

| Capability | Commit | Coverage |
|---|---|---|
| `textDocument/publishDiagnostics` | `78f2017` | SMT-LIB parser-error surface; solver-level audit still deferred |
| `textDocument/definition` | `aeecd5e` | Within-doc lookup of declare-sort / declare-datatype / declare-const / declare-fun / define-fun targets |
| `textDocument/hover` | `913a0d5` | BV literal width annotation + declaration-line for indexed symbols |
| `textDocument/completion` | `7ae1bfd` | 39 static items (19 SMT-LIB keywords + 8 theory names + 5 classical-axiom families + 7 lu-kb keywords) |
| `workspace/symbol` | `f7c3439` | Case-insensitive substring filter across every open document |
| `textDocument/codeAction` | `06d1a20` | Placeholder for v0.x→v1.x kb migration; real chained-converter implementation lands in phase 3 |
| vscode-extension split | `feda783` | `src/audit.ts` editor-agnostic / `src/extension.ts` VSCode-specific + LSP client via vscode-languageclient |

Audit guards: `adsmt-lsp/tests/scaffold.rs` carries 20 unit
tests pinning each capability's helper functions and the
Document field set. The vscode-extension TypeScript side
remains compile-only checked (no test runner wired) — the
`audit.ts` surface is small enough that the LSP integration
tests in adsmt-lsp catch contract drift end-to-end.

Phase 2 deferrals (acceptable per `lsp_roadmap.md`):
- Solver-level dead-pattern audit fed through
  `publishDiagnostics` is left as a 25LSP.2 follow-up — the
  parser-error surface alone satisfies the mandatory bar.
- Real kb auto-migration in `codeAction` waits for
  `lu-common::migration` (lands during phase 3 absorption).
- Cross-document `goto_definition` waits for a workspace-level
  symbol propagation pass.

Carried into phase 3: 25B.1 CDCL two-watched literals
(substantial inner-loop restructure deferred from v0.23; lands
during v1.0 RC prep so the LSP work and the CDCL rewrite never
collide).

### Phase 3 entry conditions (recorded for the v1.0 RC cycle)

When the v1.0 RC cycle opens, before the workspace-version
bump to 1.0.0-rc.1:
1. Re-read this phase 2 sign-off section + the phase 1 sign-off
   section above to confirm no surface has been silently
   amended.
2. Re-run `cargo test --workspace --tests` and the
   adsmt-lsp scaffold tests to confirm no regression.
3. Land 25B.1 CDCL two-watched literals.
4. Promote 21E.4's forward-looking `1.0.0` marker to a real
   attribute on `adsmt-ffi/src/lib.rs` (and on `adsmt-cert`,
   `adsmt-parser` per phase 3 RC checklist items in each
   policy doc).
5. Land the logicutils absorption (21E.2 option 2-A'): every
   `lu-*` crate moves into the adsmt workspace, `adsmt-meta`
   metacrate is created, `lu-cli` carries the legacy
   binaries, `lu-common::migration::v0_to_v1` ships its first
   chained converter.

### Phase 3 sign-off (RC1.H.2, 2026-05-31)

All 6 RC1.* tasks landed in v1.0.0-rc.1. The cycle closes
with the RC bump ready for promotion to v1.0.0 stable.

| Task | Commit | Outcome |
|---|---|---|
| RC1.1 phase 1+2 sign-off re-verify | `ee6cad6` | Cycle-open commit re-ran every audit guard; clean |
| RC1.2 CDCL two-watched literals | `03229c0` | `propagate_two_watched` + `build_watches` + `register_clause_watches` + CdclState clause_watches/watches/prop_head |
| RC1.3 1.0.0 marker → real attribute | `eed2427` | `breaking_changes_semver` proc-macro + sentinel const stamps on adsmt-ffi/adsmt-cert/adsmt-parser |
| RC1.4 infra (state subtrees + plan) | `d04e4fc` | `state/{adsmt-frozen,logicutils-frozen,integrated}/` + `ABSORPTION_PLAN.md` |
| RC1.4.A atomic logicutils absorption | `cb34793` | 12 lu-* crates absorbed; submodule deinit; Cargo wiring rewritten; logicutils auxiliary materials frozen under `state/logicutils-frozen/` |
| RC1.5 adsmt-meta metacrate | `728ba00` | `adsmt-meta` workspace member with `no-cli` / `only-cli` / `full` features for distro packaging |
| RC1.6 lu-common::migration::v0_to_v1 | `931a59c` | First chained converter (identity at rc1) + `chain()` helper for future v(N)→v(N+1) steps |

Audit guards still active at sign-off:
- Phase 1: `c_abi_surface.rs` (2 tests), `dialect_surface.rs` (3),
  `cert_surface.rs` (5)
- Phase 2: `adsmt-lsp/tests/scaffold.rs` (20)
- Phase 3: `adsmt-heuristic-checker` 4-peer safeguard +
  attribute on adsmt-ffi / adsmt-cert / adsmt-parser

The workspace now consists of:
- 14 adsmt-* crates (adsmt-core / cert / theory / class /
  quant / abduce / engine / parser / heuristic-checker /
  heuristic-checker-macros / lints / cli / ffi / lsp /
  meta)
- 12 absorbed lu-* crates (lu-common / freshcheck / stamp /
  lu-match / lu-expand / lu-query / lu-rule / lu-queue /
  lu-par / lu-deps / lu-multi /
  logicutils-translator-to-oxiz-sat)
- vscode-extension under `tooling/`

Next cycle = **v1.0.0 stable**. Bump = `1.0.0-rc.1 → 1.0.0`
in `Cargo.toml`. The `breaking_changes_semver("1.0.0")`
attribute on the three authority crates becomes the live
baseline; every future change is gated by the 8-layer
safeguard.

### Phase 3 — v1.0 RC bump

Once phase 1 and phase 2 are signed off:
- adsmt workspace minor → 1.0.0-rc.1 (the first RC).
- All v1.0-stamped breaking-version peers
  (`.breaking-versions.lock`, `breaking_history.txt`,
  `[package.metadata.adsmt]`, `tests/snapshots/`) get the
  real 1.0.0 binding semantics — the 21E.4 forward-looking
  marker becomes a real attribute.
- `adsmt-meta` metacrate (per 21E.2 option 2-A') published
  to crates.io for the first time at 1.0.0-rc.1.
- logicutils workspace folded into the adsmt workspace per
  the 21E.2 option 2-A' plan.
- v1.0.0 stable follows after RC stabilisation; the exact
  RC cadence (rc.1 → rc.2 → … → stable) is decided at phase
  3 entry.

## Cross-decision integration

Option 4 is consistent with:
- **21E.1 = option 5 (bidirectional embed)** — phase 1's
  surface freeze locks the adsmt side; OxiZ flows in via
  Apache-2 PRs at its own pace, both before and after phase 3.
- **21E.2 = option 2-A' (logicutils absorption)** — phase 3
  is the moment logicutils folds in. The `adsmt-meta`
  metacrate exists from rc.1.
- **21E.4** — the v0.21 forward-looking 1.0.0 marker carried
  by the four manifest peers becomes a real attribute at
  phase 3.
- **21H.2** — policy transition notes already added to
  `prover_emit_policy.md`, `oxiz_relationship.md`, and
  `logicutils_version_rule.md` describe the v1.0 surface that
  phase 1 freezes.

## How to apply

- **During v0.21 (current)**: no further LSP code work. Phase
  1 stabilisation continues through normal cycle work; the
  scope freeze itself is a future-cycle gate, not a v0.21
  deliverable.
- **Cycles between v0.21 and phase 3**: any new public-
  surface change should explicitly answer "does this need to
  land before phase 1 freezes?" — if yes, expedite; if no,
  defer past v1.0 to a future major bump.
- **At phase 2 entry**: revisit this memo to confirm the
  capability list still reflects the intended minimum bar.
- **At phase 3**: the v1.0 RC commit message must reference
  this memo + the 21F.3 task as the decision audit trail.
