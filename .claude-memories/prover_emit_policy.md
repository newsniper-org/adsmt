---
name: prover_emit output policy across ITPs
description: Cross-ITP emit policy — full proof-bearing source declarations, term-mode primary with tactic-mode fallback; Lean emit is the reference and Rocq/Isabelle out-of-tree projects mirror it exactly. Ltac1 entirely excluded for Rocq. On-demand classical-axiom imports with strict file-level checking.
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# `prover_emit` output policy (cross-ITP)

**Confirmed 2026-05-29 (UTC).** Applies to:
- `adsmt-cert::lean_emit` (in-tree, dual-target Lean 4 + OxiLean)
- `adsmt-emit-rocq` (out-of-tree, `~/adsmt-contrib/adsmt-emit-rocq`)
- `adsmt-emit-isabelle` (out-of-tree,
  `~/adsmt-contrib/adsmt-emit-isabelle`)
- any future ITP emit project

## Policy summary

**Output form**: a complete ITP source file (`.lean` / `.v` / `.thy`)
consisting of a sequence of full *proof-bearing source
declarations*. NOT a standalone tactic snippet, NOT a verdict-only
text dump.

**Term vs tactic**: hybrid — term-mode is primary, tactic-mode is
the fallback wrapper for steps whose explicit term is verbose or
not yet reconstructed:
- Trivial steps (`Refl`, theory axiomatize, abductive marker)
  emit term-mode declarations (`:= rfl`, `axiom`, `:= sorry` /
  `Admitted.`).
- Compound kernel rules (`Trans`, `EqMp`, `Deduct`, `Abs`, `Beta`,
  `Inst`, `InstType`) emit tactic-mode blocks with the *correct*
  statement type — proof body is currently a tactic-level `sorry`
  / `admit` stub pending v0.17 deepening, but the kernel still
  type-checks the declaration.
- Final conclusion is a single `theorem result : <concl> :=
  s<final>` (or the ITP-specific equivalent).

## Lean emit (reference shape)

For Lean 4 (and OxiLean — substantially Lean 4-compatible per
`oxilean_syntax_investigation.md`):

| cert StepBody | Lean emit |
|---|---|
| `Assume(φ)` | `axiom s<i> : φ` |
| `Refl(t)` | `theorem s<i> : t = t := rfl` |
| `Trans { lhs, rhs }` | `theorem s<i> : <concl> := by sorry  -- Eq.trans s<lhs> s<rhs>` (v0.17 → `Eq.trans s<lhs> s<rhs>`) |
| `EqMp { iff, p }` | `theorem s<i> : <concl> := by sorry  -- (s<iff>).mp s<p>` (v0.17 → `(s<iff>).mp s<p>`) |
| `Deduct`/`Abs`/`Beta`/`Inst`/`InstType` | `theorem s<i> : <concl> := by sorry  -- <hint>` |
| `Theory { name, witness, parents }` | `axiom s<i> : <concl>` + comment block carrying witness summary |
| `Assumed { φ, explain }` | `theorem s<i> : φ := sorry  -- abductive: <explain>` |
| Final conclusion | `theorem result : <concl> := s<final>` |

Wrapping: `namespace AdsmtCert ... end AdsmtCert`. Free term
variables emit as `axiom <name> : Prop` (per Bool→Prop semantic
decision in `prover_emit::common`).

## Rocq emit (mirror — Ltac1 EXCLUDED)

**Strict mirror of the Lean shape.** Rocq surface syntax differs
but the cert step → declaration mapping is one-to-one.

### File header (always emitted)

```rocq
From Stdlib Require Import Logic.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Ltac2".
```

The `Set Default Proof Mode "Ltac2"` line is mandatory — Ltac1
(classic Ltac) is **excluded entirely** as legacy. Every
`Proof. ... Qed.` block in the emitted file elaborates as Ltac2.

This implies a hard floor of **Rocq 8.10+** (when Ltac2 entered
the standard distribution). Earlier Rocq versions are out of
scope. (If a consumer is locked to pre-8.10 they need a separate
prelude file aliasing the few Ltac2-only spellings we use.)

### Per-step mapping

| cert StepBody | Rocq emit (Ltac2) |
|---|---|
| `Assume(φ)` | `Axiom s<i> : φ.` |
| `Refl(t)` | `Theorem s<i> : t = t. Proof. reflexivity. Qed.` |
| `Trans { lhs, rhs }` | `Theorem s<i> : <concl>. Proof. eapply eq_trans; [exact s<lhs> | exact s<rhs>]. Qed.` (stub: `Admitted.`) |
| `EqMp { iff, p }` | `Theorem s<i> : <concl>. Proof. apply (proj1 s<iff>); exact s<p>. Qed.` (stub: `Admitted.`) |
| `Deduct`/`Abs`/`Beta`/`Inst`/`InstType` | `Theorem s<i> : <concl>. Admitted. (* TODO: kernel-rule reconstruction *)` |
| `Theory { name, witness, parents }` | `Axiom s<i> : <concl>. (* theory '<name>'; witness: <summary> *)` |
| `Assumed { φ, explain }` | `Theorem s<i> : φ. Admitted. (* abductive: <explain> *)` |
| Final conclusion | `Theorem result : <concl>. Proof. exact s<final>. Qed.` |

Wrapping: `Module AdsmtCert. ... End AdsmtCert.`. Free term
variables emit as `Parameter <name> : Prop.` (per Bool→Prop
semantic decision).

**Why `Theorem` over `Definition`**: cert reflection requires only
verification, not transparency. `Theorem ... Qed.` is opaque and
matches the proof-irrelevance flavour of the propositional
fragment we emit.

**Why classic tactics survive the Ltac2 floor**: the basic tactics
we use (`reflexivity`, `apply`, `exact`, `eapply`, `admit`) all
have Ltac2 forms that share the Ltac1 syntactic shape, so the
mapping table above reads the same regardless of proof-mode
selection. Ltac1 is excluded as a *language*, not as a vocabulary.

## Isabelle/HOL emit (mirror)

Strict mirror of the Lean shape. Isabelle theory files use the
Isar proof language.

### File header (always emitted)

```isabelle
theory AdsmtCert
  imports Main
begin
```

Closing: `end`.

### Per-step mapping

| cert StepBody | Isabelle/HOL emit |
|---|---|
| `Assume(φ)` | `axiomatization where s<i>: "φ"` (or `consts` for symbol-level) |
| `Refl(t)` | `lemma s<i>: "t = t" by simp` |
| `Trans { lhs, rhs }` | `lemma s<i>: "<concl>" using s<lhs> s<rhs> by (rule trans)` (stub: `sorry`) |
| `EqMp { iff, p }` | `lemma s<i>: "<concl>" using s<iff> s<p> by blast` (stub: `sorry`) |
| `Deduct`/`Abs`/`Beta`/`Inst`/`InstType` | `lemma s<i>: "<concl>" sorry  -- TODO: kernel-rule reconstruction` |
| `Theory { name, witness, parents }` | `axiomatization where s<i>: "<concl>"  (* theory '<name>'; witness: <summary> *)` |
| `Assumed { φ, explain }` | `lemma s<i>: "φ" sorry  -- abductive: <explain>` |
| Final conclusion | `theorem result: "<concl>" using s<final> by simp` |

Free term variables emit as `consts <name> :: "bool"` (the
Isabelle `bool` sort is the proposition family in HOL — distinct
from Rocq's `Prop` but semantically the same role).

## Common-module anchors

The shared semantic decisions live in
`adsmt-cert::prover_emit::common` (or its out-of-tree
counterpart that imports the in-tree module via the
`adsmt-cert` crate dep):

1. **adsmt `Bool` ⇒ prover-side `Prop`** (Lean / Rocq) or
   prover-side `bool` (Isabelle). Atoms are *propositions*, not
   computable booleans.
2. **Theory steps axiomatized** — same in all three.
3. **Abductive markers become explicit holes** (`sorry` /
   `Admitted.` / Isabelle `sorry`).
4. **Compound kernel rules emit correct statement types with
   proof-side stub** — kernel type-checks; tactic-level proof
   reconstruction is v0.17 work.
5. **Free variables become axioms / parameters of the
   proposition family**.

## Classical axiom imports (on-demand)

**Adopted 2026-05-29** in response to ypeg's request
`.local-requests-from/ypeg/2026-05-29-classical-axiom-on-demand.md`.
**Implementation landed in adsmt v0.18.0 (2026-05-29).** Full
8-layer offline safeguard active; lean_emit / adsmt-emit-rocq /
adsmt-emit-isabelle ship matching import injection. Mid-block +
pattern-marker cert AST reified; adsmt-minimum heuristic table
authored in lu-kb. cargo-dylint plugin lifted to cdylib +
feature-gated nightly path.
Default emit is **intuitionistic-safe** — classical-axiom imports
only land in the header when a step in the cert demonstrably
requires them. The whole machinery is offline-first: precompile-
time checks gate emit; CI/network unavailability never weakens the
safety net.

### Markers on Step

Each [`Step`] carries two hint markers, each pairing with an
allowlist of classical modules:

| Marker | Options | Default |
|---|---|---|
| `should_import_classical` | (none — opt-in by presence) | `∅` |
| `allow_to_import_classical` | `{ lazy: bool, scan: bool }`, both default off | `∅` |

`should` truth-table: presence forces every allowlist member into
the file header regardless of usage analysis.

`allow` truth-table (per marker instance):

| `lazy` | `scan` | semantics |
|---|---|---|
| off | off | gatekeeper only — `should ⊆ ⋃ allow` is a file invariant; no import on its own |
| off | on  | `scan` ignored — same as off/off |
| on  | off | include iff the same module is requested by some sibling `should` in the file |
| on  | on  | include iff the rendered output contains the module's axioms (post-hoc text scan) |

Multiple markers of the **same kind with identical options**
collapse to one (allowlist union). Different-option `allow`
markers coexist and evaluate independently; their import
contributions union additively.

### Marker attachment layering (D1.A = δ' + D1.A-2 = δ+ε)

Markers attach at four layers, all contributing additively to the
file's import decision:

```
per-step  →  per-mid-block  →  per-cert  →  per-emit-call
```

The **mid-block** layer is optional. Each `MidBlock` is a
strictly-nested Rust-block-inspired scope with `local_markers` and
`exported_markers`, plus a `contents: Vec<MidBlockItem>` of step
references and nested sub-blocks. Cert producers freely introduce
or omit mid blocks; consumers must not assume any structure.

### Pattern markers (cross-cutting)

In addition to lexical blocks, a `PatternMarker { pattern,
markers }` attaches markers to **any step matching the pattern**.
`StepPattern` is a closed Rust enum:

```rust
enum StepPattern {
    Theory(String),
    Kind(StepKindTag),
    IdRange(RangeInclusive<StepId>),
    And(Vec<StepPattern>),
    Or(Vec<StepPattern>),
    Not(Box<StepPattern>),
}
```

Boolean completeness via `{And, Or, Not}`. Convenience helpers
`StepPattern::xor`, `at_most_one`, `exactly_one` desugar via the
standard equivalences (`a XOR b ≡ (a ∨ b) ∧ ¬(a ∧ b)`;
`AtMostOne(vs) ≡ ¬(⋁_{i<j} v_i ∧ v_j)`;
`ExactlyOne(vs) ≡ AtMostOne(vs) ∧ ⋁ vs`).

Pattern markers and block markers compose by independent additive
union (D1.A-1.pat.interact = α). Dead pattern detection (a
declared pattern matching 0 steps) is **silent in normal
compilation**; only `cargo dylint` invocation runs the analysis
and emits `Warn`-level diagnostics under lint name
`adsmt_dead_heuristic_pattern`. The dylint plugin lives in a
shared workspace member that also hosts lu-kb-side lints
(γ' — type-sharing aware, supports the v1.0 logicutils+adsmt
merger).

### Classical module hierarchy (D4 = δ)

Two-level enum: a small cross-ITP **family** + precise per-ITP
**variant**.

```rust
enum ClassicalModuleFamily {
    Propositional,   // Rocq: Classical_Prop; Lean: Classical.em; Isabelle: no-op
    Predicate,       // Rocq: Classical_Pred_Type; Lean: Classical.choice (limited)
    Choice,          // Rocq: ClassicalEpsilon; Lean: Classical.choice
    FunExt,          // Rocq: FunctionalExtensionality; Lean: funext
}
```

Per-ITP precise enums live in each backend
(`adsmt-cert::lean_emit`, `adsmt-emit-rocq`, `adsmt-emit-isabelle`).
Family → precise is a per-backend mapping table.

### Per-step required-set heuristic

| Step kind | Family-level required | Reason |
|---|---|---|
| `Assume` / `Refl` / `Trans` / `EqMp` / `Beta` / `Abs` / `Deduct` / `Inst` / `InstType` | `∅` | HOL kernel rules — intuitionistic |
| `Theory { name in {LIA, LRA, EUF, Arrays, Datatypes, BV, Polite} }` | `∅` | adsmt theory ground reasoning — intuitionistic |
| `Theory { witness: Drat{..} }` (D5 = α) | `{Propositional}` | SAT proofs use LEM; **always** Classical_Prop |
| `Theory { name: "bool", … }` (ypeg's term) (D6 = β) | (absorbed by DRAT row above) | adsmt's boolean reasoning routes through DRAT |
| `Assumed { φ, … }` | `∅` | abductive hole — classical-irrelevant |
| `Instance` | `∅` | type-class — intuitionistic |

Bool→Prop reflection (D9 = β) **does not** trigger any classical
import by mere occurrence; only steps whose witness actually
invokes LEM/NNPP do.

### Parent classical-ness inheritance (D7 = δ')

Each step carries a pair `(direct_required, transitive_required)`.
Inheritance is **pair-to-pair**: a parent's direct contribution
promotes one hop into the child's transitive slot; the parent's
transitive contribution stays in the child's transitive.

```
child.direct      = child.own_intrinsic
child.transitive  = child.own_intrinsic ∪ ⋃_{p ∈ parents} (p.direct ∪ p.transitive)
```

Steps with parent references (8 kinds: `Trans / EqMp / Deduct /
Abs / Inst / InstType / Theory / Instance`) participate.

### Emit-time check (D1.E)

Strict, hard-failing, no escape hatch:

1. For every step *s* in the cert, compute `required(s)` per the
   heuristic table.
2. Aggregate file-level `resolved_imports` = file's `should`
   markers ∪ file's `allow` markers' evaluated contributions.
3. For every pair `(s, m)` where `m ∈ required(s) \
   resolved_imports`, emit a compile-time error naming `s` and
   `m` (D1.E-2 = δ pair-level).
4. **No escape hatch** (D1.E-3 = α) — neither emit-call nor
   per-step force-intuitionistic is offered.
5. If `required(s) ≠ ∅` for some step but the cert has **zero**
   markers anywhere, emit error — no silent auto-promote
   (D1.E-4 = α).

### Heuristic table (reference-set source)

The check's reference set is built from two contributions
combined at lu-kb authoring time:

- **adsmt-side minimum heuristic table** — the immutable floor.
- **user-defined extension heuristics** — append-only.

Both are written in lu-kb (with the lu-kb DSL **untouched** —
hard premise). Top-level constructs used: `Fact + Rule + EnumDef
+ DataDef + Relation + Instance + Constraint` (D1.E-1.A-1' =
γ + δ + Constraints).

The lu-kb source is loaded via three triple-form Rust proc-macros
hosted in `adsmt-heuristic-checker-macros` (D1.E-1.A-2):

```rust
adsmt_heuristics! { /* inline lu-kb */ }
import_adsmt_heuristics!("file.kb")
#[derive_heuristics("file.kb")]
```

Both forms parse the lu-kb at proc-macro time (D1.E-1.A-3 →
`compile_error!("…")` on failure; D1.E-1.A-4 → source-file-
relative path resolution).

### Non-contradiction validation

The heuristic ruleset must be **logically non-contradictory**
(D1.E-1.B = constraint-driven). The non-contradiction conditions
are themselves written as lu-kb `constraint` blocks and verified
by a SAT instance (D1.E-1.B-2 = ε).

Two-tier verification (D1.E-1.B-1 hybrid):

- **adsmt minimum table** → checked **once at adsmt-side
  development** by `external/oxiz/oxiz-sat` directly, via the new
  translator subcrate `external/logicutils/logicutils-translator-
  to-oxiz-sat` (deterministic + injective lu-kb → CNF mapping;
  D1.E-1.C). The validated minimum table ships as an embedded IR.
- **user-defined extension heuristics** → checked **per user
  crate** by `adsmt-heuristic-checker` (a slim Rust subcrate
  depending on `adsmt-core + adsmt-cert + adsmt-theory`,
  B-1-2.2 = γ) sitting on top of the embedded minimum IR.

User-extension fragment (D1.E-1.B-1-3 = β'): adsmt theory
capabilities (LIA / LRA / EUF / Arrays / Datatypes / BV / Polite)
auto-decide which lu-kb constructs are supported (B-1-3.3 = γ).
HKT is **strictly forbidden** (no `KindExpr::Arrow` / `Slot`;
`TypedArg.kind_ann` ∈ `{None, Some(Type)}` only). Lambdas are
allowed only with **zero external capture** (free-variable set
empty after excluding lambda params; compile-time constant
captures like `EnumDef` constructors are an exception).

Validation cost is **unbudgeted** (B-1-5.cmn — POSIX `timeout`
CLI handles operational caps). Incomplete verification (timeout)
= compile error (B-1-5.cmn-d4 → strict completeness, α).

### Per-user IR cache

Validated user-extension IR caches under each user crate's
`OUT_DIR` (B-1-4 = γ). Cache key incorporates:

- adsmt minimum table hash (α),
- `adsmt-heuristic-checker` version (β),
- `#![breaking_changes_semver(...)]` attribute lower-bound (δ').

A user IR cache is valid iff the path from old → current contains
**zero** `breaking_changes_semver` attributes strictly between.
The newest attribute's semver auto-sets the lower bound for all
future compatibility checks.

### v0.x exclusion policy (adopted 2026-05-29)

The 8-layer safeguard treats adsmt's pre-1.0 line as
**completely out of scope**. Concretely:

- Every layer silently drops `major == 0` entries from its
  canonical view (see `retain_in_scope` in
  `adsmt_heuristic_checker::breaking_versions`).
- v0.x → v0.y, v0.x → v1.y, and v1.x → v0.y are **all**
  unguarded — no forward or backward compatibility checks fire.
- v1.0.0 is the first version that anchors the safeguard.
- v0.x snapshots may still be vendored under
  `tests/snapshots/vX.Y.Z/` for historical reference, but the
  regression test ignores them.

Until v1.0.0 ships the safeguard is wiring that's exercised by
tests but never blocks a build for a compatibility reason.

### 8-layer offline safeguard (cmn-e = σ+γ+ε+ι+κ+π+τ+λ)

Peer-equal layers (coord-1 = δ) all mirror the same
`breaking_changes_semver` information; divergence between any two
is an error.

| Layer | Mechanism |
|---|---|
| σ | `include_str!(".breaking-versions.lock")` + proc-macro compile-time compare |
| γ | `.breaking-versions.lock` lockfile + build.rs check |
| ε | append-only manifest `breaking_history.txt` |
| ι | snapshot regression test (`tests/snapshots/<version>/`) |
| κ | parameterised property-test (expected-version enumeration) |
| π | `pre-commit` hook (`just install-breaking-hook`, opt-in) |
| τ | dual source: attribute + `Cargo.toml [package.metadata.adsmt.breaking_versions]` |
| λ | monotonic K12-256 double-pass hash const + frozen-hash file |

Hash design (λ-1):

- Algorithm: **KangarooTwelve-256** (lu-common exposes it as a new
  optional feature `k12`, fresh-published as patch bump — λ-1-b
  = γ' + δ + β + β).
- Double pass with two customization strings:
  - `cs_primary = "adsmt-breaking-versions-v1-primary"`
  - `cs_shadow  = "adsmt-breaking-versions-v1-shadow"`
- Validation requires both hashes match (λ-1-a'.pol = δ); a
  diagnostic trace lists every (layer, hash-slot) outcome on
  divergence. Trace format = JSON Lines + human-readable text;
  emitted when env var `ADSMT_HEURISTIC_TRACE=1` is set.
- Canonical normalization (λ-1-a'.store = δ): internal `[u8; 64]`
  flat (primary∥shadow); public API offers lowercase hex
  `"<primary>:<shadow>"` and struct `HashPair { primary, shadow }`.

Customization rotation (λ-1-a'.cs-roll = α): the `v1` token
co-rotates with `adsmt-heuristic-checker`'s major semver. v2 →
`"…-v2-primary"`, etc.

### Compatibility-check escape

The compatibility regression test (κ + ι) cannot be disabled in
any profile other than `dev`. The `dev` profile may opt out
(B-1-5.4 = "절대로 끌 수 없음" outside dev). Concrete mechanism
selected at implementation time (`cfg(debug_assertions)` based).

### Cross-prover translation of family-level imports

| Family | Lean 4 | Rocq (Ltac2 mode) | Isabelle/HOL |
|---|---|---|---|
| `Propositional` | (built-in `Classical.em`) | `From Stdlib Require Import Classical_Prop.` | (no-op — `Main` is classical) |
| `Predicate` | (built-in `Classical.choice` w/ caveats) | `From Stdlib Require Import Classical_Pred_Type.` | (no-op) |
| `Choice` | `Classical.choice` | `From Stdlib Require Import ClassicalEpsilon.` | (no-op) |
| `FunExt` | `funext` | `From Stdlib Require Import FunctionalExtensionality.` | (no-op) |

Importable lines land **after** the existing fixed prelude lines
(e.g., `From Ltac2 Require Import Ltac2.`) and **before** the
`Module AdsmtCert.` wrapper.

## Lessons / future

- The three emit modules MUST stay in lockstep on the semantic
  decisions above. The common module is the single anchor;
  changes to the anchor propagate consistently to all three
  emits.
- If a fourth ITP target appears (HOL Light, Agda, …), it
  reuses the same anchors and adds its own out-of-tree project
  following the `adsmt-emit-<itp>` naming convention.
- Tactic / proof-body reconstruction (v0.17 deepening) replaces
  the `sorry` / `Admitted.` stubs with real terms; the table
  shapes don't change, only the right-hand side of each stub
  row.
- This policy is stable; only the v0.17 reconstruction work
  amends it. Any *form* change (e.g. switching to a
  result-only emit, or to a Definition-only term-mode-only
  emit) would be a major architectural revision and gets
  recorded separately.
