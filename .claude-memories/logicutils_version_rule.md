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

Patch bumps remain independent — logicutils may patch ahead of
adsmt for additive feature work and vice versa.

Current state:
- adsmt v0.19.x ⇔ logicutils v0.21.x

Intervening logicutils minors (0.19, 0.20) are intentionally
skipped — they belong to the post-restoration accounting, not
the live version line.

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

## 3. Merge plan at adsmt v1.x — 3-way unification (revised 2026-05-13)

Once adsmt reaches v1.x stability — the point at which the C ABI,
SMT-LIB dialect, and proof certificate format are committed (per
sec 34 Q68 / Q66) — the v1.0 release **unifies three projects**:

  adsmt v1.0  =  adsmt-core + logicutils + OxiZ (integrated form)

Originally this was a 2-way (adsmt + logicutils) merge plan. Revised
2026-05-13 when the user adopted Path A+B for OxiZ (see
`oxiz_relationship.md`). The third leg — OxiZ — joins as either a
pinned dependency or as the *substrate* into which adsmt folds (P5
in `oxiz_relationship.md` chooses).

Targets for the unified workspace:
- lu-kb is the user-facing kb surface
- OxiZ provides SAT + classical SMT theories + math + proof
- adsmt provides abductive engine + HOL+HKT kernel + type-class
  layer + Lean4 first-class + lu-kb integration
- the unified version drops the "+2" offset (logicutils becomes
  1.0.0; OxiZ continues its own line as upstream)

**How to apply**: don't preemptively merge before v1.x. Until then,
maintain rules (1) and (2) for logicutils, run the OxiZ phased
integration (P1-P5) per `oxiz_relationship.md`, and re-check the
unified vision at every v0.x → v0.(x+1) bump.

**Tracking**: re-check this plan whenever OxiZ has a material
release or adsmt reaches a phase milestone.
