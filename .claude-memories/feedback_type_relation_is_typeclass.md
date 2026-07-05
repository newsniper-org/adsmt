---
name: feedback-type-relation-is-typeclass
description: "'type relation' is adsmt's own term for a TYPE CLASS — one and the same concept across the whole project; never frame them as two systems needing integration."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

Across all of adsmt, **"type relation" IS the type-class concept** — the user has said this many times. `adsmt-class/src/lib.rs` literally opens *"Type-class layer (T_class) for adsmt"*; `Relation`/`Instance`/`Resolver`/`Dict`/`Law`, the *Like family, lawful-by-proof instances, and the four-way interlock are all the one type-relation = type-class system. A relation's `'p` is a **type-relation predicate parameter** (`Relation::pred_params` / `Instance::preds`). The relation-level `'p` is now resolved BOTH at admission (`Dict::pred` / `AdmissionDict`) AND at **use sites** (`InstanceMatch::pred_dict` / `::pred(name)`, `8d542ce` #344 — `Resolver::resolve` surfaces the matched instance's concrete predicates with the head-match σ applied, the use-site analogue of `Dict::pred` and the type-relation-level realisation of the fn-level §5.2 dictionary-passing). NOTE: `Preserving('p)` as a type relation was RETIRED — preservation is a higher-order *predicate*, see [[feedback-preservation-is-higher-order-predicate]].

**Why:** I repeatedly framed "lukb has no type-class surface" / "adsmt-class is a separate Rust-API layer" as if connecting two foreign concepts (even spun up a workflow to "discover" whether a type-class notion exists). That mis-models the project — the type-relation layer already exists; what's missing is only a **surface** that declares it.

**How to apply:** Treat the lukb work as *lukb gaining a `relation`/`instance` declaration surface* for the existing type-relation (= type-class) layer — NOT a novel "lukb↔class integration." Use "type relation" as the project's term for type class; don't separate them. See [[four-way-interlock-design-intent]], [[lawful-type-relation-instances]], [[numberlike-family-design]], [[nat-wnat-refinement-collapse]] (the `'p` work).
