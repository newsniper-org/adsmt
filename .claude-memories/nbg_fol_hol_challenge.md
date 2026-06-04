---
name: NBG → FOL/HOL translation as adsmt self-challenge
description: Internal challenge proposed during the §3 meta-compiler discussion — translate NBG set theory's finite axiomatisation (Gödel 18 / Bernays 8) into adsmt-core's FOL/HOL surface so adsmt can ingest NBG axioms directly and verify set/class reasoning.
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
NBG (von Neumann–Bernays–Gödel set theory) is a **finitely
axiomatisable** alternative to ZFC: where ZFC uses
schema-based axioms (Comprehension, Replacement), NBG packs
them into a fixed list of class-quantified axioms (Gödel 1940
gives 18; Bernays 1937 gives 8 after consolidation).  NBG and
ZFC prove the same first-order sentences about sets.

**Our challenge** (proposed alongside the §3 meta-compiler
discussion): translate the NBG axioms into the adsmt-core
HOL+HKT surface so adsmt can ingest them directly as input
formulas and *verify set/class reasoning end-to-end*.

**Why this is distinct from §3 work:**
This is a kernel-input exercise, not an engine refactor.  It
exercises adsmt's quantifier handling on a small but very
quantifier-heavy benchmark and tests whether our HOL surface
is expressive enough to model class quantification.  Useful as
a stress test independent of Verus pressure.

**Concrete sub-challenges:**

1. **Class quantification mapping.**  NBG distinguishes `∀x.
   …` (range over sets) from `∀X. …` (range over classes,
   including proper classes).  adsmt-core's HOL is
   predicative rank-1 polymorphic — direct class
   quantification is not built in.  The translation has to
   pick:
   - Encode classes as `Bool`-valued predicates over a base
     `Set` type (Russell-style: class = its characteristic
     function), or
   - Introduce a `Class` sort separately and reify `∈` as a
     two-place relation between `Set` and `Class`.
   The choice affects how cleanly the NBG schemas land.

2. **Finite axiomatisation preservation.**  NBG's selling
   point over ZFC is that Comprehension is replaced by 8
   class-existence axioms (B1–B8 in Bernays' presentation:
   ∈-relation, complement, intersection, domain, product,
   converse, association, permutation).  The translation
   needs to keep this finiteness — encoding via an axiom
   schema defeats the purpose.

3. **Quantifier-heavy axioms as §3.2 trace candidates.**
   Foundation/Regularity, Replacement, and Choice are
   quantifier-heavy and structurally repetitive.  If §3.2
   meta-tracing JIT lands, these axioms make natural
   benchmarks for algebraic-invariant guards (the
   "skeleton match modulo α-renaming" guard variety in
   particular).

4. **Cert export.**  Lean4 has `mathlib`-style ZFC
   encodings; Rocq has classical set theory libraries;
   Isabelle/HOL has `ZF` and `HOLCF`.  None target NBG
   natively.  The cert emitter would need a per-prover
   "NBG → host meta-theory" lowering pass.  Mizar (built
   on Tarski-Grothendieck, which extends NBG with
   inaccessible cardinals) is the most natural target if
   the cert ever grows a Mizar emitter.

**Status:** noted as a self-imposed challenge — no commit
yet, no roadmap slot.  Picks up when the §3 sub-cycles
quiet down or when we want a quantifier-heavy benchmark
independent of Verus pressure.
