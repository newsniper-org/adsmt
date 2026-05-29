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
| v0.17 | 0.17.0 (closed 2026-05-29) | P4 — upstream coordination, prover_emit refactor for OxiLean + Lean4 co-equal sibling targets (Rocq and other ITPs out-of-tree, per 2026-05-28 user directive), cert text-emission (NOT FFI), compound-rule reconstruction, LFSC proof term reconstruction, E-matching congruence-closure deepening, Tier 3 quantifier enumeration, BV bit-level fact propagation, Arrays extensionality, LinArith Fourier-Motzkin closure + Simplex bridge, abductive SLD chaining, parser lu-kb integration. Language-binding work DEFERRED until user's `leo4` library v1.0 (local repo `~/leo4/`). |
| v0.18 | 0.18.0 (closed 2026-05-29) | Classical-axiom-imports (on-demand) pipeline per ypeg's 2026-05-29 request: per-step `should_import_classical` / `allow_to_import_classical` markers with `(lazy, scan)` truth table, four-layer additive attachment, closed-enum `StepPattern` + desugar helpers, hierarchical classical-module families + per-ITP precise variants, strict hard-failing emit-time check, pair-to-pair parent inheritance, `adsmt-heuristic-checker` subcrate + `adsmt-heuristic-checker-macros` proc-macros + `adsmt-lints` (runtime audit + JSON for IDE), adsmt-minimum heuristic lu-kb table + 8-layer offline safeguard (σ+γ+ε+ι+κ+π+τ+λ) with KangarooTwelve-256 double-pass frozen hash via `lu-common::k12`, mid-block + pattern-marker cert AST, v0.x exclusion policy adopted (pre-1.0 is out of scope for the safeguard). Follow-up deepening: A/B/C/F/G/H/I/J + K (Rocq Trans/EqMp only)/L scaffold/M lightweight + P/Q operational. |
| **v0.19** | **0.19.0 (current — opened 2026-05-29)** | **P5 — v1.0 architectural decision** + v0.18 carry-over deepening + DPLL(T) engine maturation + theory deepening + quantifier work + tooling + CI + benchmarks. **Mid-cycle progress as of 2026-05-29 mid-audit**: K-full compound-rule proof terms (Lean+Rocq+Isabelle) ✓; A.4 J-full proc-macro OUT_DIR auto-use ✓; A.5 scan=true two-pass wiring ✓; B.4 nested push/pop audit ✓; C.2 LinArith introspection API ✓; C.3 Arrays store-store normalisation ✓; C.5 Polite multi-sort + disagreement diagnostic ✓; E.3 C ABI header + policy ✓; F.1 VS Code extension scaffold ✓; F.2 lu-smt --audit-json ✓; G.1 criterion benchmark suite ✓; G.2 GitHub Actions CI ✓; G.3 status timeseries ✓; G.4 contrib docs polish ✓. **Pending**: A.2 L-full (LFSC parser), A.3 M-full (E-graph), B.1-3 (DPLL(T) main loop), C.1 (BV bit-blasting), C.4 (Datatypes recursive), D.1-3 (Quantifier tier 4 + HOL + SLD typed unification). **Awaiting user decision**: E.1 (adsmt ⇔ OxiZ), E.2 (v1.0 unification plan), E.4 (first v1.0 breaking attribute), F.3 (LSP exploration scope), H.2 (v1.0 transition notes). logicutils v0.x-smt at 0.21.0 per the restored +2 offset rule.** |
| v0.21 | 0.21.0 (planned) | First post-v1.0-decision cycle. Concrete shape depends on the v1.0 architectural decision in v0.19. |

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
  next applicable cycle name (`v0.19` for current cycle work,
  `v0.21` for post-v1.0-decision work).
- The corresponding logicutils version follows the **restored
  "+2 offset"** rule per `logicutils_version_rule.md` (the v0.17
  audit's match-minor rule was rolled back at the v0.19 cycle
  boundary). adsmt 0.19 ⇔ logicutils 0.21; patch bumps remain
  independent.
