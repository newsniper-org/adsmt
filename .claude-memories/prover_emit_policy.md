---
name: prover_emit output policy across ITPs
description: Cross-ITP emit policy — full proof-bearing source declarations, term-mode primary with tactic-mode fallback; Lean emit is the reference and Rocq/Isabelle out-of-tree projects mirror it exactly. Ltac1 entirely excluded for Rocq.
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
