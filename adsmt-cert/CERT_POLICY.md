# adsmt certificate format policy

**Status**: **v0.23 phase 1 freeze candidate** (v1.0 RC
pre-commit). Per `lsp_roadmap.md` phase 1 / task 23A.3. The
certificate AST + emit shapes enumerated below are intended as
the v1.0.0 cert surface; any modification after v0.23 sign-off
requires either a deliberate v1.x major bump or a re-opening
of the freeze decision.

## Certificate AST (`adsmt-cert::canonical`)

The top-level type is `Certificate`. Its frozen fields:
- `steps: Vec<Step>` — ordered proof steps.
- `conclusion: StepId` — the step proven last.
- `mid_blocks: Vec<MidBlock>` — Rust-block-inspired metadata
  containers (v0.18 scaffold).
- `pattern_markers: Vec<PatternMarker>` — cross-cutting
  pattern markers attached at the certificate level.

`Step` carries:
- `id: StepId(u32)` — stable handle.
- `sequent: Sequent` — `(hypotheses, conclusion)` pair over `Term`.
- `body: StepBody` — which inference rule produced this step.
- `source_loc: Option<SourceLoc>` — file/line/col provenance.
- `should_import_classical: ClassicalSet` — caller-injected
  classical-axiom import hint.
- `allow_to_import_classical: Vec<AllowMarker>` — caller-
  injected allow markers.
- `mid_block: Option<MidBlock>` — pattern-marker carrying
  metadata produced by the v0.18 mid-block scaffold.

### StepBody — 12 frozen variants (inference rules)

Aligned with the 12 inference rules in `adsmt-core`. Adding
new variants in v1.x minor bumps is allowed; renames or
removals require a major bump.

| Variant | Inference rule |
|---|---|
| `Assume(Term)` | hypothesis introduction |
| `Refl(Term)` | reflexivity of `=` |
| `Trans { lhs, rhs }` | transitivity of `=` |
| `Abs { var, eq }` | abstraction (lambda intro on equality) |
| `Beta { redex }` | β-reduction step |
| `EqMp { iff, p }` | modus ponens via biconditional |
| `Deduct { a, b }` | deduction theorem (`a ⊢ b ⇒ ⊢ a → b`) |
| `Inst { sigma, thm }` | term substitution into a theorem |
| `InstType { sigma, thm }` | type substitution into a theorem |
| `Theory { name, witness, parents }` | theory-side proof (UF/EUF/LIA/LRA/BV/Arrays/Datatypes/Polite) |
| `Instance { relation, types, witness }` | type-class instance discharge |
| `Assumed { formula, explain }` | abductive marker (`sorry`-shaped) |

### Classical-axiom marker surface

Already declared frozen by `adsmt-parser/DIALECT_POLICY.md`
and `prover_emit_policy.md`. Mirrored here for the full
sign-off list:

- `ClassicalModuleFamily` (closed enum) — module hierarchy.
- `ClassicalSet` — set of required modules.
- `AllowMarker` — one allow-instance carrying a `StepPattern`.
- `StepPattern` — closed enum with `Theory` / `Kind` /
  `IdRange` / `And` / `Or` / `Not`, plus the derived
  helpers `xor` / `at_most_one` / `exactly_one`.
- `PatternMarker` — name + source_loc payload.
- `MidBlock` + `MidBlockItem` — Rust-block-inspired mid-step
  metadata container.

### Source-position surface

- `SourceLoc { file, line, col }` — frozen shape; `file` is
  workspace-relative.

## S-expression emit (`adsmt-cert::emit`)

Authoritative byte form. Round-trips: parse the emitted S-expr,
materialise a `Certificate`, re-emit, compare → byte-identical.

The S-expr emit shapes for the 12 `StepBody` variants are
pinned by `adsmt-cert/tests/` (existing round-trip cases plus
the new `cert_surface.rs` audit).

## Per-ITP emit families (frozen interface)

Three emit modules consume the same `Certificate` and produce
different surface output:

- `adsmt-cert::lean_emit::emit_lean(&Certificate) -> String`
  — Lean 4 reference shape.
- `adsmt-cert::prover_emit::lfsc_parse::render_lean / render_rocq
  / render_isabelle(&LfscDocument) -> String` — round-trip
  through the LFSC parser for already-LFSC-encoded proofs.
- Out-of-tree backends (`adsmt-emit-rocq`, `adsmt-emit-isabelle`)
  consume `adsmt-cert::prover_emit::common` anchors. The
  lockstep policy in `prover_emit_policy.md` keeps them
  byte-identical to the Lean reference for the corresponding
  step shapes.

The function signatures above are part of the freeze; output
*content* changes are constrained by `prover_emit_policy.md`
(specifically the per-step mapping tables for Lean / Rocq /
Isabelle).

## Pre-publication checklist (v1.0 entry)

Phase 1 (v0.23) freeze candidate sign-off status:

1. **StepBody variant audit** — ✅ enforced by
   `tests/cert_surface.rs::stepbody_variant_set_is_frozen`.
2. **StepPattern variant audit** — ✅ same test file pins the
   6 closed variants + the 3 derived helpers.
3. **Round-trip smoke** — ✅ existing cert emit/parse tests.
4. **Per-ITP signature audit** — ✅ same test file pins the
   public emit function signatures.
5. **`#![breaking_changes_semver("1.0.0")]`** — registered as
   the forward-looking marker per 21E.4; phase 3 RC bump
   promotes it to a real attribute on `adsmt-cert/src/lib.rs`.
6. **S-expr output byte stability** — TBD; phase 3 RC will
   freeze the exact emit bytes per variant.

Sign-off threshold: items 1, 2, 3, 4 mandatory for phase 1;
items 5, 6 mandatory for phase 3 RC.

## How to amend this document

- Additive changes (new StepBody variant for a new inference
  rule, new ClassicalModuleFamily entry): append below the
  relevant table with a `[since vX.Y]` annotation; no freeze
  re-opening required.
- Subtractive or shape-changing edits: out of scope for v0.x →
  v1.0 transition. Stage them as v2.x candidates in a
  separate post-merge audit.
