---
name: adsmt ⇔ logicutils v0.x-smt relationship
description: Versioning rule, immediate-sync rule for kb syntax, and the v1.x merge plan
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
The adsmt project and the `v0.x-smt` branch of logicutils (vendored at
`external/logicutils/`) follow three coordinated rules during the
pre-1.0 cycle. All three were set by the user; do not deviate without
asking.

## 1. Version offset — restored to "+2 offset" (2026-05-29 by
##    user policy at the v0.19 cycle boundary)

  logicutils v0.x-smt minor = adsmt minor + 2

History:
- 2026-05-12 (original): adopted "+2 offset" rule.
- 2026-05-29 (v0.17 mid-cycle audit): relaxed to match-minor
  because both workspaces had converged.
- 2026-05-29 (v0.19 cycle open): **restored** the original "+2
  offset" per user policy. The 0.18.0 → 0.21.0 logicutils jump
  re-establishes the gap.
- 2026-05-29 (v0.21 cycle open): rule preserved. adsmt 0.19 →
  0.21 bump pairs with logicutils 0.21.0 → 0.23.0. Same
  intervening-minor-skip convention (0.22 is reserved
  bookkeeping, not a live release).

Patch bumps remain independent — logicutils may patch ahead of
adsmt for additive feature work and vice versa.

Current state:
- adsmt v0.21.x ⇔ logicutils v0.23.x

Intervening logicutils minors (0.19, 0.20, 0.22) are
intentionally skipped — they belong to the post-restoration
accounting, not the live version line.

**How to apply**: when bumping adsmt's workspace MINOR version,
bump `external/logicutils/Cargo.toml`'s
`[workspace.package].version` to (adsmt minor + 2). The inline
comment in each workspace's Cargo.toml documents the rule and
records the restoration moment.

## 2. Immediate kb-syntax sync (set 2026-05-13)

When an adsmt version bump introduces any lu-kb surface change, the
corresponding logicutils v0.x-smt commit lands **in the same cycle**,
not deferred:

- New kb keyword, AST item, or parser shape  →  add to
  `lu-common/src/kb/{lexer,ast,parser}.rs`.
- New lu-kb block or directive               →  document in
  `docs/man/lu-kb.5`.
- New surface that lu-query/lu-rule should ignore safely → add a
  no-op arm in `lu-query/src/engine.rs` so the workspace still builds.
- Bump logicutils version per rule (1) in the same commit.

**Why**: keeps adsmt and lu-kb in lockstep so downstream tools that
consume kb files never see a syntax error caused by an adsmt feature
that hasn't been mirrored yet. Past breach example: v0.3 adsmt
shipped Boolean/quantifier/datatype work without lu-kb reflection,
which we corrected by adding `enum` syntax in the v0.5 logicutils
bump (option C).

**How to apply**: include the logicutils submodule change in the
same conceptual unit as the adsmt change. Update the parent repo's
submodule pointer afterward so the two repos move together.

## ABSORPTION COMPLETED — v1.0.0-rc.1 RC1.4.A (2026-05-31)

The logicutils absorption settled on 2026-05-30 (per option
2-A') executed atomically in the **RC1.4.A** commit. The
submodule `external/logicutils/` at frozen SHA `283c6d7` has
been deinitialised and removed; the 12 `lu-*` crates now live
as top-level workspace members alongside `adsmt-*`.

Final layout (post-absorption):

| Crate | Location |
|---|---|
| `lu-common` | `lu-common/` |
| `freshcheck` | `freshcheck/` |
| `stamp` | `stamp/` |
| `lu-match` | `lu-match/` |
| `lu-expand` | `lu-expand/` |
| `lu-query` | `lu-query/` |
| `lu-rule` | `lu-rule/` |
| `lu-queue` | `lu-queue/` |
| `lu-par` | `lu-par/` |
| `lu-deps` | `lu-deps/` |
| `lu-multi` | `lu-multi/` |
| `logicutils-translator-to-oxiz-sat` | `logicutils-translator-to-oxiz-sat/` |

Pre-merge logicutils auxiliary materials (LICENSE, README,
docs/, packaging/, pre-merge Cargo.toml) preserved under
`state/logicutils-frozen/` as the immutable audit trail.

The version-offset rule (§1 below) is **historically frozen**
— since v1.0.0-rc.1 every absorbed crate inherits the adsmt
workspace version directly (`version.workspace = true`
resolves to `1.0.0-rc.1`). The kb-syntax sync rule (§2) also
retires: source and consumer now live in the same workspace,
so coupling is enforced by the compiler.

## 3. Merge plan at adsmt v1.x — concretised 2026-05-30 (option 2-A')

P5 v1.0 decision (`oxiz_relationship.md` §"P5 outcome", chosen
2026-05-30) settled on **bidirectional embed** for OxiZ — adsmt
stays a separate project. The logicutils side of v1.0 was
decided the same day under the **21E.2 option 2-A'** plan:

**Concrete v1.0 shape:**
- **Full absorption of logicutils into the adsmt workspace** —
  every `lu-*` crate (`lu-common`, `lu-kb`, `lu-match`,
  `lu-expand`, `lu-query`, `lu-rule`, `lu-queue`, `lu-par`,
  `lu-deps`, `lu-multi`, `logicutils-translator-to-oxiz-sat`)
  becomes a top-level workspace member alongside `adsmt-*`
  crates.
- **`v0.x-smt` AND upstream `main` both fold in** — upstream
  `main` is confirmed-frozen (no new development), so adsmt
  v1.0 is the joint successor of both branches. The external
  `external/logicutils/` submodule is archived after the
  fold.
- **CLI binaries preserved** — `lu-cli` (or per-tool crates)
  hosts the legacy `lu-kb`, `lu-query`, `lu-rule`, …
  binaries with identical names, so existing distro
  packaging (`logicutils` package on Arch / Debian /
  Ubuntu / Devuan / Knoppix) continues to resolve.
- **`adsmt-meta` metacrate** publishes the "everything"
  entry point for Linux distro packaging. Cargo
  `[features]` exposed: `only-cli` (just the CLI surface),
  `no-cli` (lib-only), `full` (default, library + every
  CLI), and theory-/backend-specific flags as needed.
- **Permanent migration logic** — `lu-common::migration`
  carries `v0_to_v1`, `v1_to_v2`, … chained converters so
  any old kb file flows through the right sequence of
  one-step migrations regardless of how far the user is
  behind. Each step is preserved forever (no v2.0 cleanup
  drop).
- **In-repo state separation** — directories are explicitly
  carved out:
  - `state/adsmt-frozen/` — frozen snapshot of pre-merge
    adsmt state (`.claude-conversations/`,
    `.claude/projects/-home-ybi-AD1/memory/`,
    `.adsmt-status/`, …)
  - `state/logicutils-frozen/` — frozen snapshot of
    pre-merge logicutils state
  - `state/integrated/` — fresh post-merge state going
    forward, *strictly separated* from the two frozen
    subtrees
  Cross-contamination between integrated and frozen
  subtrees is forbidden; each frozen subtree is read-only
  audit material.
- **+2 offset rule retires** — logicutils 0.23 (paired with
  adsmt 0.21) is the last separate-line release. v1.0 has
  no offset because everything is one workspace under
  matching version.
- **License flow** — logicutils is BSD-2-Clause; absorbed
  into adsmt's BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later
  triple. BSD-2 is one-way compatible with the triple, so
  no relicensing work is required (the user's LGPL
  question 2026-05-30 confirmed the "modification-free use
  doesn't trigger LGPL copyleft" reading anyway).

**Why option 2-A' over plain 2-A**: plain absorption would
have stranded existing logicutils CLI users; the
metacrate + binary-preservation + auto-migration trio is
what makes the absorption observable as a "continuation"
rather than a discontinuity from the user perspective.

**How to apply** (during v0.21 cycle and any pre-merge
work):
- New kb-syntax changes still follow rule §2 (immediate
  sync) until the absorption lands.
- New `lu-*` work in the submodule should be tagged "carry
  through to v1.0" so the merge sequencing can find every
  unmerged change at fold time.
- `state/` separation is a hard invariant — any in-repo
  state added during v0.21 (e.g. `precompact-backups-N.md`)
  should already be earmarked for the appropriate
  subdirectory at v1.0 fold time.

**Tracking**: this plan is the v1.0 contract; re-check
only on a material OxiZ release, an adsmt milestone, or
direct user instruction to revise.
