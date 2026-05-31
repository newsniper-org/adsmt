# logicutils absorption plan (RC1.4)

**Status**: v1.0.0-rc.1 RC1.4 lays the infrastructure (state
subtree segregation, this plan document); the **actual move
of `lu-*` crates** lands as `RC1.4.A` — a follow-up commit
that performs the git-subtree-style merge in a single atomic
operation so the workspace never spends time in a half-folded
state.

This document is the contract for RC1.4.A.

## Decisions (already settled)

- **21E.2 option 2-A'** — full absorption with metacrate + CLI
  preservation + perpetual auto-migration (see
  `memory/logicutils_version_rule.md` §3).
- **Subtree-style fold** — every `lu-*` crate moves into the
  adsmt workspace as a top-level member; git history is
  preserved by walking the submodule with a subtree-style
  merge so the absorption commit shows the full logicutils
  commit lineage in `adsmt`'s `git log`.
- **State segregation** — `state/{adsmt-frozen,logicutils-frozen,integrated}/`
  hard-separated; cross-contamination forbidden.

## Crates to absorb

From `external/logicutils/` (v0.x-smt branch at 0.25.0):

| Crate | New workspace location |
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

## Cargo wiring changes (executed in RC1.4.A)

- `Cargo.toml` `[workspace] members` gains all 12 new entries.
- `[workspace] exclude` keeps `external/oxiz`; the
  `external/logicutils` entry is removed.
- Every path dep `../external/logicutils/<crate>` is rewritten
  to `../<crate>`. Affected manifests:
  - `adsmt-parser/Cargo.toml` (lu-common)
  - `adsmt-heuristic-checker/Cargo.toml` (lu-common + translator)
- `external/logicutils` submodule removed from `.gitmodules`
  (the submodule pointer becomes the archival marker — last
  `v0.x-smt` commit hash recorded in this plan + commit
  message before the entry is removed).
- The absorbed crates' `Cargo.toml` headers strip the
  `[workspace]` section and the per-crate
  `version.workspace = true` is rebound to the adsmt
  workspace version (i.e. the absorbed crates inherit
  `1.0.0-rc.1` rather than carrying their old 0.25.0).
- License field on each absorbed crate is reviewed: lu-*
  crates were BSD-2-Clause; under absorption they continue as
  BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (the
  user's LGPL question 2026-05-30 confirmed
  modification-free use doesn't trigger LGPL copyleft, so
  the one-way upgrade is safe).

## Carry-over from logicutils

- `lu-cli` crate (new in absorption) hosts the legacy
  `lu-kb`/`lu-query`/`lu-rule` `[[bin]]` definitions so
  distro packaging on Arch / Debian / Ubuntu / Devuan /
  Knoppix continues to resolve.
- `lu-common::migration` (created by RC1.6) starts with the
  `v0_to_v1` converter; chains every subsequent v(N) → v(N+1)
  converter under the same module.

## Frozen state subtrees (already set up in RC1.4)

Created in this commit ahead of the fold:
- `state/adsmt-frozen/` — receives the pre-merge adsmt state
  snapshot at RC1.4.A time.
- `state/logicutils-frozen/` — receives the pre-merge
  logicutils state snapshot.
- `state/integrated/` — post-merge state going forward.

## Sequencing

1. **RC1.4** (this commit) — infrastructure: `state/`
   subtrees + this plan document.
2. **RC1.4.A** — the absorption commit itself. Atomic — one
   commit moves every `lu-*` crate, updates Cargo wiring,
   archives the submodule pointer, and stamps the
   absorption summary in `memory/logicutils_version_rule.md`
   §3.
3. **RC1.5** — `adsmt-meta` metacrate (depends on RC1.4.A).
4. **RC1.6** — `lu-common::migration::v0_to_v1`.

RC1.4.A is large enough to deserve its own commit; landing
RC1.4 first lets the workspace continue to build and tests
to pass while the moving parts are planned out.
