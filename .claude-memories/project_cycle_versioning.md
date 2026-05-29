---
name: adsmt cycle vs Cargo version mapping
description: Cycle names referenced in code comments ("v0.5", "v0.13", "v0.15") map directly to adsmt's Cargo workspace minor version
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
adsmt's development happens in *cycles* whose names appear as
`vX.Y` in source comments. **A cycle name IS the Cargo
workspace minor version at that time.** Concretely:

| Cycle | Cargo version when cycle landed | Focus |
|---|---|---|
| v0.1 | 0.1.0 | core kernel + cert skeleton |
| v0.3 | 0.3.0 | quantifier loop, lu-kb assertion routing |
| v0.5 | 0.5.0 | theory layer alpha (BV/FP placeholders), CaDiCaL backend |
| v0.7 | 0.7.0 | source-position scaffolding, recorder maturation |
| v0.9 | 0.9.0 | SAT backend survey, oxiz fork preparation |
| v0.11 | 0.11.0 | P1 — `oxiz_backend` |
| v0.13 | 0.13.0 | P2 — oxiz-math wired, hand-rolled LIA retired |
| v0.15 | 0.15.0 (closed 2026-05-16) | P3 — proof byte-form pipeline, source-loc end-to-end, Lean reflection initial, oxiz-contrib-abduction + oxiz-contrib-bindings spinouts. Archival branch `v0.15` pinned at merge SHA |
| **v0.17** | **0.17.0 (current)** | **P4 — upstream coordination, prover_emit refactor for **OxiLean + Lean4 co-equal sibling targets** (Rocq and other ITPs out-of-tree, per 2026-05-28 user directive), cert text-emission (NOT FFI), compound-rule reconstruction, LFSC proof term reconstruction, E-matching congruence-closure deepening. Language-binding work DEFERRED until user's `leo4` library v1.0 (local repo `~/leo4/`).** |
| v0.19 | 0.19.0 (planned) | P5 — v1.0 decision (adsmt absorbed into oxiz vs stays separate frontend) |

**Why:** Confirmed 2026-05-16 by user. The codebase has many
comments like `// v0.5 brings Simplex` or `// placeholder for
v0.1` — these are cycle markers, not arbitrary version labels.
When the cycle ships, the version bumps to match (0.13.0 brought
Simplex, 0.15.0 brought the proof bridge, etc.).

**How to apply:**
- When auditing stale "vX.Y" comments, check the table above: if
  the cycle has passed and the feature is implemented, replace
  the marker with a current-state description (or drop it).
- When writing new comments referring to future work, use the
  next applicable cycle name (`v0.17` for P4 work, `v0.19` for P5
  / v1.0 decisions).
- The corresponding logicutils version is *adsmt minor + 2* per
  `logicutils_version_rule.md`, so adsmt 0.15 ⇔ logicutils 0.17
  (after the user's manual sync bump).
