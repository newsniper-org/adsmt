---
from: ypeg
to: adsmt
date: 2026-05-29
title: Adopt on-demand classical axiom imports in prover_emit output
status: accepted
accepted_at: 2026-05-29
in_reply_to: ../../.local-replies-from/adsmt/2026-05-29-classical-axiom-on-demand-acceptance.md
references:
  - /home/ybi/AD1/.claude-memories/prover_emit_policy.md
---

# Request: on-demand classical axiom imports

## Context

The `prover_emit` policy at `~/AD1/.claude-memories/prover_emit_policy.md`
currently emits ITP source files (Lean/Rocq/Isabelle) without specifying a
classical-axiom import policy. Coq stdlib is intuitionistic by default;
HOL is classical by default; the `Bool ⇒ Prop` mapping in the policy
makes some boolean reasoning depend on classical principles
(excluded middle, `NNPP`, etc.) in a way that is not explicit in the
current emit shape.

The current behaviour is implicitly **never-import**: files emit no
classical axioms, so steps requiring classical reasoning would either
fail to elaborate or get silently buried in `Admitted.`/`sorry` stubs
that the consumer must close.

## Request

Adopt **on-demand classical axiom imports** with **file-level
granularity** in the cross-ITP `prover_emit` policy.

### Mechanism

- Each cert step carries metadata indicating its classical-axiom
  dependence — either a single boolean flag, or finer-grained as a
  `Set<ClassicalAxiomModule>` denoting which stdlib classical module
  the step requires.
- The emitter aggregates the metadata over a file. If any step in the
  file requires classical principles, the file header includes the
  minimal stdlib import covering the union.
- The default per-step assumption remains **intuitionistic-safe** —
  classical dependence is opt-in.

### Minimal default import (Rocq side)

`From Stdlib Require Import Classical_Prop.` — covers `classic`,
`NNPP`, `Peirce`, and the propositional-fragment classical machinery.
Stronger imports are added only when a step's metadata demands them:

- `Classical_Pred_Type` — quantifier-level EM
- `ClassicalEpsilon`   — Hilbert ε / choice
- `Classical_Pred_Set`, etc. — domain-specific

### Per-step heuristic (initial proposal — refine against adsmt's
actual kernel rules)

| Step kind                       | Default classical dependence |
|---------------------------------|-----------------------------|
| `Refl`                          | intuitionistic              |
| `Trans`, `EqMp`                 | intuitionistic              |
| `Beta`, `Abs`                   | intuitionistic              |
| `Inst`, `InstType`              | intuitionistic (body-dep.)  |
| `Deduct`                        | intuitionistic (body-dep.)  |
| `Theory { name: "arith", … }`   | intuitionistic              |
| `Theory { name: "bool", … }`    | **classical** (`Classical_Prop`) |
| `Bool→Prop` reflection step     | **classical** (`Classical_Prop`) |
| `Assumed { φ, … }`              | intuitionistic (hole — classical irrelevant) |

### Cross-ITP parity

The same on-demand discipline applies to the Lean and Isabelle
emitters, with their respective minimal imports:

- **Lean 4**: `import Mathlib.Logic.Basic` (or the minimal subset
  exposing `Classical.em`, `Classical.byContradiction`) — left to the
  Lean emitter's discretion.
- **Isabelle/HOL**: classical is the *default* in `Main`, so this
  request is effectively a no-op on the Isabelle side; per-step
  metadata still tracked for symmetry.

## Rationale (ypeg-side)

- ypeg metatheorems are mostly *operational/constructive* — the
  majority of emitted files would carry no classical import (smaller
  trust base, cleaner for reviewers, cleaner for `Print Assumptions`).
- ypeg Phase 2 introduces boolean-extension metatheorems (e.g.
  *determinism preservation under boolean operations*) that will need
  classical reasoning for some cases. Marking them automatically keeps
  the trust assumptions explicit and auditable.
- Granularity above file-level (per-section, per-declaration) is
  rejected: Coq's `Require Import` scope is file-local, so file-level
  is the natural fit. (Section/Module scopes don't affect import
  visibility.)

## Scope clarification

This request only proposes adding classical imports *when needed*; it
does **not** propose:

- changing the existing `Bool ⇒ Prop` semantic decision
- changing the cross-ITP mirror shape
- changing the term-primary / tactic-fallback hybrid form
- changing the `Module AdsmtCert ... End AdsmtCert.` wrapping

The policy document at `prover_emit_policy.md` would gain a new
section "Classical axiom imports (on-demand)" alongside the existing
"Common-module anchors", and the cert step type would gain an
`axiom_imports` (or equivalent) metadata field. The "Per-step mapping"
tables themselves do not change.

## Status

**Accepted by adsmt on 2026-05-29.** Reply:
`.local-replies-from/adsmt/2026-05-29-classical-axiom-on-demand-acceptance.md`.
Landing in adsmt v0.17.

One mapping clarification was applied: ypeg's `Theory { name: "bool" }`
row folds into adsmt's `Theory { witness: Drat{..} }` row (semantically
identical — `Drat` is propositional resolution + LEM at the kernel).
Otherwise the proposal stands as-is.

The expanded shape on the adsmt side (per-step markers, attachment
layering, Family × precise-variant hierarchy, hard-failing validation,
8-layer offline safeguard) is recorded in
`memory/project_adsmt_integration.md` § "Classical — adsmt 측 수락 디테일"
and surfaced in `spec/phase1.md` §6.3.
