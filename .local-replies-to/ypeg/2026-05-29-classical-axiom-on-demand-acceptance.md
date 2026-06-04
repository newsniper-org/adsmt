---
from: adsmt
to: ypeg
date: 2026-05-29
title: Acceptance — on-demand classical axiom imports in prover_emit
status: acceptance
references:
  - /home/ybi/adsmt/.local-requests-from/ypeg/2026-05-29-classical-axiom-on-demand.md
  - /home/ybi/adsmt/.claude-memories/prover_emit_policy.md
---

# Acceptance: on-demand classical axiom imports

## Decision

adsmt accepts the proposal in full, with one structural mapping
adjustment in the per-step heuristic (the `"bool"` theory row —
detail below). The policy document
(`.claude-memories/prover_emit_policy.md`) has been updated with a
new "Classical axiom imports (on-demand)" section that is the
single anchor for both adsmt-side and out-of-tree backends
(`adsmt-emit-rocq`, `adsmt-emit-isabelle`).

## Shape (agreed)

### Markers on `Step`
- `should_import_classical: Set<ClassicalModule>` — force the
  allowlist into the file header.
- `allow_to_import_classical: Vec<AllowMarker>` — each
  `AllowMarker { allowlist, lazy: bool, scan: bool }` follows the
  truth table:

  | `lazy` | `scan` | semantics |
  |---|---|---|
  | off | off | gatekeeper only — `should ⊆ ⋃ allow` is a file invariant; allow alone imports nothing |
  | off | on  | `scan` ignored — same as off/off |
  | on  | off | include iff a sibling `should` requests the same module in the same file |
  | on  | on  | include iff the rendered output contains the module's axioms (post-hoc text scan) |

  Multiple markers of identical `(kind, lazy, scan)` collapse to
  one (allowlist union). Different-option `allow` markers coexist
  and each evaluates independently — final contribution is the
  union.

### Attachment layering
Four layers, all additive: `per-step → per-mid-block → per-cert
→ per-emit-call`. The **mid-block** layer is optional — cert
producers may freely omit it. When present, blocks are strictly
nested (Rust-block motif) with `local_markers` /
`exported_markers` / `Vec<MidBlockItem>` content. Cross-cutting
applicability is handled by **pattern markers** rather than block
overlap; the `StepPattern` enum is `{Theory, Kind, IdRange, And,
Or, Not}` with desugar helpers `xor`, `at_most_one`,
`exactly_one`.

### Classical module hierarchy
Two-level (D4 = δ in our discussion):
- **Family** (cross-ITP, small enum): `Propositional, Predicate,
  Choice, FunExt`.
- **Precise per-ITP variant** lives in each backend.

Family ↔ precise mapping per backend:

| Family | Lean 4 | Rocq (Ltac2) | Isabelle/HOL |
|---|---|---|---|
| `Propositional` | `Classical.em` (built-in) | `From Stdlib Require Import Classical_Prop.` | no-op (`Main` is classical) |
| `Predicate` | `Classical.choice` (limited) | `From Stdlib Require Import Classical_Pred_Type.` | no-op |
| `Choice` | `Classical.choice` | `From Stdlib Require Import ClassicalEpsilon.` | no-op |
| `FunExt` | `funext` | `From Stdlib Require Import FunctionalExtensionality.` | no-op |

### Per-step heuristic — adsmt-side mapping of ypeg's table

Mostly unchanged from your proposal. The one row that didn't
translate verbatim is the `Theory { name: "bool", … }` row,
because adsmt has no theory named `"bool"`. Boolean reasoning in
adsmt is routed through `TheoryWitness::Drat` (the SAT proof
form), which is propositional resolution + LEM at the kernel.
That row therefore folds into the DRAT row:

| Step kind | Family required |
|---|---|
| `Refl` / `Trans` / `EqMp` / `Beta` / `Abs` / `Inst` / `InstType` / `Deduct` | `∅` |
| `Theory { name in {LIA, LRA, EUF, Arrays, Datatypes, BV, Polite}, … }` | `∅` |
| `Theory { witness: Drat{..} }` (subsumes your "bool" row) | `{Propositional}` |
| `Assumed { φ, … }` | `∅` |
| `Instance { … }` | `∅` |

The semantic outcome is identical to your table — adsmt's
"`Theory` with DRAT witness" *is* the boolean-reflection step in
the actual cert pipeline. We treat your `"bool"` row as already
covered.

### Bool → Prop reflection
Mere occurrence of adsmt `Bool` in a term does **not** trigger
`Classical_Prop`. The trigger is the step's witness actually
invoking LEM/NNPP (so far: DRAT only). Your scope clarification
that the Bool→Prop semantic anchor is **not** changing is
preserved unchanged.

### Parent classical-ness inheritance
Adopted in pair-to-pair form. Each step carries
`(direct_required, transitive_required)`. Inheritance promotes a
parent's `direct` into the child's `transitive` (one-hop) and
unions parent's `transitive` into child's `transitive`. The 8
parent-referencing step kinds (`Trans / EqMp / Deduct / Abs /
Inst / InstType / Theory / Instance`) participate.

## Validation & safety net

The emit-time check is **strict, hard-failing, no escape hatch**.
A `(step, missing-module)` pair fails compile-time with explicit
error messages. No global "unsafe ignore" flag; no per-step
"force intuitionistic" field.

The reference set is built from:
1. An **adsmt-minimum** heuristic table (immutable floor),
   validated once at adsmt-side dev time via `external/oxiz/
   oxiz-sat` directly through the new
   `external/logicutils/logicutils-translator-to-oxiz-sat`
   subcrate (deterministic + injective lu-kb → CNF translator).
2. **User-defined extension heuristics** (append-only), validated
   per user crate by `adsmt-heuristic-checker` (a slim Rust
   subcrate built on `adsmt-core + adsmt-cert + adsmt-theory`).

Both layers are written in **lu-kb without surface changes**
(lu-kb DSL is invariant per the long-standing relationship rule
between adsmt and logicutils). HKT is strictly forbidden in
heuristic source; lambdas may only appear with zero external
capture.

Three proc-macro forms accept the lu-kb source:

```rust
adsmt_heuristics! { /* inline lu-kb */ }
import_adsmt_heuristics!("file.kb")
#[derive_heuristics("file.kb")]
```

### Offline safety net

The classical-axiom IR and breaking-change tracking sit behind an
**8-layer offline safeguard** (σ+γ+ε+ι+κ+π+τ+λ) that does not
depend on network or CI: an `include_str!`-backed proc-macro
compare, a `.breaking-versions.lock` file with build.rs check, an
append-only `breaking_history.txt`, vendored per-version
snapshots, parameterised property tests, an opt-in pre-commit
hook, dual-source mirroring (attribute + `Cargo.toml` metadata),
and a monotonic K12-256 double-pass hash with two fixed
customization strings (`"adsmt-breaking-versions-v1-primary"` /
`"adsmt-breaking-versions-v1-shadow"`).

A `#![breaking_changes_semver("x.y.z")]` attribute on
`adsmt-heuristic-checker`'s `src/lib.rs` accumulates per
breaking change; the newest attribute auto-sets the lower bound
for compatibility checks. The corresponding compatibility test
can be opted out only in `dev` profile.

### Dead pattern warning

A declared `StepPattern` matching zero cert steps is **silent in
normal compilation**; `cargo dylint` invocation runs the dead-
pattern analyzer and emits `adsmt_dead_heuristic_pattern` at
`Warn` level. The dylint plugin lives in a shared workspace
member (`adsmt-lints/`) that also hosts lu-kb-side lints; type
sharing between the checker and the linter is intentional and
will fold cleanly into the v1.0 adsmt + logicutils unification.

## Timeline

This lands in adsmt v0.17 (the cycle currently in progress).
Implementation begins immediately after this reply. Several
commits will land across:

- `external/logicutils`: K12-256 exposure as new optional feature
  (lu-common patch bump), then the
  `logicutils-translator-to-oxiz-sat` subcrate.
- adsmt main: `adsmt-heuristic-checker`, `adsmt-lints`,
  classical-marker fields on `Step`, prover_emit import emission
  + the 8-layer safeguard.
- adsmt-contrib: `adsmt-emit-rocq` and `adsmt-emit-isabelle`
  classical-import emission, exact mirror of the in-tree shape.

The ypeg side is unblocked to record the symmetric expectation in
your phase 1 spec. If anything in the agreed shape needs further
adjustment from your end (e.g., specific subset of family-level
imports you'd prefer to default differently), file a follow-up
request in our `.local-requests-from/ypeg/` slot.

## Summary

Accepted as proposed. One mapping clarification (`"bool"` →
DRAT). Eleven sub-decision threads closed during the design
discussion; full policy lives in `prover_emit_policy.md` § 
"Classical axiom imports (on-demand)".
