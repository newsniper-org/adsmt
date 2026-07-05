---
name: lawful-type-relation-instances
description: "Design principle (user, 2026-06-27): a type relation (type class) may carry GOAL members (laws) alongside function/method members; an `instance` is VALID only if adsmt's own solver discharges ALL its goal-members at build time, and an instance declaration that fails any goal is BUILD-REJECTED. This is the load-bearing mechanism that makes the *Like type relations self-verifying — the concrete realization of the four-way interlock."
metadata:
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**User design (2026-06-27, across 3 messages):** let a type relation have **GOAL members** (laws/axioms), described "just like functions" (the method members). An `instance` of the type relation is admitted as VALID **only if every goal-member is successfully proven**; an instance declaration that fails any goal must be **rejected at build time** (빌드 거부). The proofs are discharged by **adsmt's own solver** — so the type-class law-checking IS the SMT/abduction engine running.

**This is the "lawful type class verified by proof" pattern — and the concrete realization of [[four-way-interlock-design-intent]]:**
- A type relation = { **method members** (operations / theory routing / reductions) } ∪ { **goal members** (the laws the carrier must satisfy) }.
- `instance IntegerLike(Int, LIA, NIA)` is valid ⟺ the solver proves IntegerLike's goal-members for `Int` (e.g. the domain constraint, discreteness, ring axioms). For `ComplexLike(ℂ, RealLike, x²+1)`, a goal-member is the minimal-polynomial law `ζ²+1 = 0` and the field axioms.
- **Type inference ↔ SMT/abduction interlock:** instance resolution (type inference) emits proof obligations (the goals), the engine discharges them, and only proven instances type-check. A bad instance = a build error, not a runtime unsoundness. This dovetails the build-time-proven **theorem packages** (LUKB_SUCCESSOR_SURFACE §7: `theorem name:` = machine-discharged, build fails on Unknown/Sat; `postulate … cite` = externally justified) — an instance's goal-members are exactly such machine-discharged obligations.

**How it shapes the `*Like` family ([[four-way-interlock-design-intent]], task #339):** every member signature (IntegerLike / RealLike / PartialIntegerLike / ComplexLike) carries, beyond its carrier/base/theory parameters, a **`laws : List Goal`** component. An instance ships its carrier + the method realizations, and the build runs each law-goal through the solver (the SAME engine hardened this session: SAT core, LIA/LRA same-pair + singleton rules #336/#337, datatype acyclicity/exhaustiveness/single-survivor #331, the verdict-gate refinement loop). Soundness of the law-check rides on that engine's soundness — which is why the z3-differential discipline ([[feedback_z3_differential_for_unsat_trust]]) is the gate for trusting any law discharged as proven.

**First concrete bite already landed:** the #337 `IntegerLike(Int)` integrality rule (`5bfe7a6`) is "the type relation deciding" — the integer carrier's defining property (integrality) is what refutes `0<x<2 ∧ x≠1`. The instance-as-proof-obligation mechanism is the natural next layer: make that defining property a GOAL-member the `Int`/`Nat`/`WNat` instances must discharge, rather than a hardcoded engine rule. Kernel home = adsmt-ir (#317, type-classes/HKT); the goal-discharge driver = the engine + the lukb verdict path (gated on #325). Build-reject path = a face/PM-level admission gate (reuse the consistency/vacuity linter [[asp-linter-design]] + the adsmt-emit PM theorem-package build gate).
