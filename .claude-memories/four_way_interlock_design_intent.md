---
name: four-way-interlock-design-intent
description: "adsmt's MOST IMPORTANT design intent (user, 2026-06-27): make TYPE INFERENCE, ABDUCTIVE-DEDUCTIVE logic, ASP, and SMT (+ HKT where applicable) organically INTERLOCK. The lukb type relation (IntegerLike(I,L,N) etc.) is the connective tissue — a higher-kinded type-class that flows type info into the reasoning engines, NOT a hardcoded per-theory hack."
metadata:
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**adsmt's most important intent (user, 2026-06-27, verbatim sense):** the FOUR — **type inference**, **abductive-deductive logic**, **ASP**, **SMT** — plus **HKT** where applicable — must **organically interlock** (서로 유기적으로 맞물리도록). This is THE unifying design goal; individual features should be evaluated by whether they strengthen that interlock.

**Concretely (the trigger):** the `IntegerLike(I, L, N)` type relation the user proposed is the FIRST instance of this — it is a **higher-kinded type-class** (kind ≈ `Type → Theory → Theory → Constraint`), e.g. `IntegerLike(Int, LIA, NIA)`, `IntegerLike(Nat, …≥1)`, `IntegerLike(WNat, …≥0)`, `IntegerLike(PeanoDatatype, …)`. It is meant to be the **connective tissue that flows TYPE information into the reasoning engines** — type inference establishes a sort is `IntegerLike`, and that instance then (a) routes it to the right SMT theory (LIA/NIA) with its domain constraint, (b) bridges a Peano-shaped datatype to ℕ so the ARITH solver discharges what the datatype solver can't, and (in the broader vision) (c) is equally usable by the ASP face and the abductive-deductive engine.

**Design implication — build the GENERAL mechanism, not the hack.** Any IntegerLike work (closing #331/#337 etc.) MUST be a general type-class / type-relation framework with an instance table, NOT a hardcoded arith special-case. The kernel home is `adsmt-ir` (the typed CIC IR, #317) where type-classes/HKT belong; the instances then drive the engine theories (`adsmt-theory`), the ASP face ([[asp-face-design]]), and abduction. The four faces already exist (SMT-LIB / lukb / ASP, abduction merged) — this is the typing layer that lets them share inferred structure.

**Why it matters here:** the prior audit ([[lukb-type-relation-utilization]]) found the type relation is currently TYPECHECK-ONLY (dropped before the solver). Realising the four-way interlock means making it a DECISION INPUT — the lever (#338) plus the IntegerLike framework. Relates to: [[lu-vs-z3-disagreement-analysis]] (the type relation is where lu could legitimately out-decide a flat-sort encoder), [[verus_emits_lukb_surface]] (the lukb surface carries the types), [[asp_face_design]] + [[abductive_smtlib_surface]] (the other two reasoning modes), and the typed kernel #317.
