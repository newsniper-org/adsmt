# Refinement types `{v:T | φ}` + generic constraint parameters `'p`

Status: **design** (extends `NAT_WNAT_REFINEMENT_COLLAPSE.md`; pre-verification
tracked). Generalises the Nat/WNat refinement-collapse into first-class
refinement types on parameters, plus *predicate polymorphism* via generic
constraint parameters. User proposal (2026-06-27).

## 1. The idea

Let a parameter's type carry a **constraint**, not just a base sort:

```
f (n : {n : Int | n > 0}) : Int          -- a constrained Int
g : {v : T | 'p(v)} -> {v : T | 'p(v)}   -- preserves an ARBITRARY constraint 'p
```

Two flavours of the predicate in `{v : T | φ}`:

- **Concrete** `q(v)` — a specific, in-scope predicate. `{x:Int | x > 0}`,
  `{xs:List | sorted xs}`. **`Nat`/`WNat` are exactly two named instances**:
  `Nat ≡ {x:Int | x ≥ 1}`, `WNat ≡ {x:Int | x ≥ 0}`.
- **Generic** `'p(v)` — a predicate **parameter**, universally bound at the
  signature (predicate polymorphism). The single quote is the disambiguator,
  decided at parse time, no inference: **`'p` is generic, `q` is concrete.**
  `{v:T | q(v)}`'s `q` is NOT generic; `{v:T | 'p(v)}`'s `'p` IS.

## 2. Concrete refinements REUSE the collapse

`{v:T | q(v)}` with a concrete `q` lowers exactly as Nat/WNat already do
(`NAT_WNAT_REFINEMENT_COLLAPSE.md`): erase to `T`'s solver sort, and `q` becomes
- a **quantifier guard** (`∀(x:{v:T|q v}). P → ∀(x:T). q(x) ⟹ P`; `∃ → ∧`),
- a **construct-site obligation** (building a `{v:T|q v}` value: prove `q(value)`),
- a **use-site hypothesis** (using one: assume `q(value)`) — the
  abduction (obligation) / deduction (hypothesis) duality.

The **pre-verified relativization lemma already covers this**: the Verus proof
(`~/nat-wnat-refinement-verification`) never cased on `dom` being `≥1`/`≥0` — it
is parametric in the guard predicate. Generalising `Dom(s)` → `Dom(φ)` for an
arbitrary `φ` re-verifies unchanged. So the concrete-refinement engine is the
existing machinery; the only change is replacing the hardcoded `refinement_lo`
(returns 1/0 for Nat/WNat) with the predicate the refinement type carries.

## 3. Kernel encoding (no new trusted surface)

Refinements are **elaboration sugar over the existing CIC kernel** — the kernel
gains nothing new, so a malformed refinement can only fail to type-check:

- `{v:T | φ}` as a **domain** ≡ `Π(v:T). φ(v) → Cod` (take a `T` plus a proof of
  `φ(v)`).
- `{v:T | φ}` as a **result** ≡ `Σ(v:T). φ(v)` (a `T` plus a proof).

The proof components are `Prop`-sorted, **proof-irrelevant, and erased at
lowering** — the SMT side only ever sees the base `T` and the predicate `φ`
(routed through the collapse). So `g : {v:T|'p v} -> {v:T|'p v}` is, in the
kernel, `Π(p:T→Prop). Π(v:T). p(v) → Σ(w:T). p(w)` — a perfectly ordinary
dependent type the kernel already checks.

## 4. Generic `'p` — dictionary-passing (chosen)

A generic constraint parameter `'p` is a `Π(p:T→Prop)` binder: predicate
polymorphism, rank-1. Quantifying over predicates is higher-order, so the SMT
boundary never sees an *uninstantiated* `'p`. We discharge it **type-relation
style** (the `adsmt-class` dictionary-passing mechanism, extended from types to
predicates):

1. **Check the body ONCE, polymorphically.** The kernel verifies the body
   against an *opaque* `'p`: from the precondition `'p(arg)` (a hypothesis),
   derive the postcondition `'p(result)` (an obligation). Because `'p` is opaque,
   the only way to discharge `'p(result)` is to exhibit `result` as `arg` (or
   another value already known to satisfy `'p`) — which is exactly what a
   constraint-*preserving* function does. This check is the **kernel's**
   (Π-over-predicate elimination — already trusted); the SMT solver is not
   involved in the polymorphic check.
2. **Instantiate at use sites.** Applying `g` at a concrete predicate `q`
   substitutes `p := q`; the **dictionary** is `q` itself plus the value-level
   proof that the argument satisfies `q`. The instantiated contract
   (precond `q(arg)`, postcond `q(result)`) is then a *concrete* refinement →
   the collapse of §2 lowers it to SMT.

So `'p` lives at the dictionary/type-relation layer (one source of truth with
the `*Like` family — see `numberlike-family-design`); only **monomorphic
instances** reach the engine. This gives the "checked once" guarantee
(monomorphisation does not) at the cost of the dictionary machinery — the
`four-way-interlock` payoff: a refinement predicate flows as a dictionary the
same way a type-class method does.

## 5. Soundness obligations (pre-verification)

1. **Parametric-predicate relativization** — generalise the Verus lemma from a
   sort-fixed `Dom(s)` to an arbitrary predicate `Dom(φ)`. Re-verifies
   unchanged (the proof is already parametric in the guard). *Trivial extension
   of the existing 7/0 proof.*
2. **Dictionary substitution** — if the body preserves an *arbitrary* `'p`
   (the polymorphic check), then it preserves any concrete `q` after
   `p := q` substitution. A substitution lemma: `(∀'p. Contract['p]) ⟹
   Contract[q]` for any `q`. This is the soundness of "check once, instantiate
   at uses". *Pre-verify in Verus alongside (1).*
3. **Proof-irrelevance / erasure** — the erased proof components never affect
   the lowered formula (the SMT side is a function of the base value + the
   predicate only). A note, not a heavy proof: the lowering structurally drops
   `Prop`-sorted Σ/→ proof arguments.

## 6. Touch-points

- **lukb face** (`adsmt-ir-lukb`): parse `{v:T | φ}` and the `'p` single-quote
  binder; elaborate to the Π/Σ kernel encoding (§3), inserting the
  construct-obligation / use-hypothesis contracts.
- **adsmt-ir-lower**: nothing for the *brace* refinement — `{v:T|φ}` elaborates
  to an explicit `Π(x:T). φ(x) → body`, which already lowers via the proof-binder
  `⟹` path. `refinement_lo` (Nat/WNat → 1/0) stays the *named-sort* hook, where
  the predicate is implicit in the sort and must be synthesised; the §2 collapse
  is unchanged.
- **adsmt-class**: predicate dictionaries for `'p` (the dictionary-pass), reusing
  the `Relation`/`Instance`/`Resolver` spine — a `'p` constraint resolves like a
  type-class constraint. **Pending** — the fn-level `'p` (above) already realises
  the *checked-once + per-fn contract* half via the kernel `Π('p)`; the
  type-relation-level `'p` adds the dictionary *registry* so a `'p` flows through
  the `Relation`/`Instance` spine across the four-way interlock.

## 7. Phasing

1. **This doc** + pre-verification of §5.1 (parametric relativization) and §5.2
   (dictionary substitution). **DONE** (`~/nat-wnat-refinement-verification`
   `src/generic_constraint.rs`, 7/0).
2. Concrete refinement types `{v:T | q}` end-to-end: lukb syntax. **LANDED**
   (`adsmt-ir-lukb`). The brace binder `{names : T | φ}` parses
   (`parser.rs::binder`), elaborates as a domain guard with the pre-verified
   polarity (`∀ → ⟹`, `∃ → ∧`; `elab.rs::elab_quant`, `refinement` arm), and
   round-trips through the printer (`printer.rs::print_quant`). The comparison
   sugar `(n:T) op rhs` is exactly the single-predicate special case
   (`refinement_generalises_the_comparison_constraint` proves they elaborate to
   the *same* kernel term). **Key simplification vs the original sketch: the
   lukb path needs NO change to `adsmt-ir-lower`'s `refinement_lo`.** That hook
   is only for the *named-sort* path (Nat/WNat), where the predicate is implicit
   in the sort and must be synthesised. A brace refinement carries `φ` as an
   explicit kernel term, so the elaborator emits `Π(x:T). φ(x) → body`
   directly — which already lowers via the existing proof-binder `⟹` path
   (`adsmt-ir-lower` `inline_refinement_lowers_to_a_guard_via_the_proof_binder`).
   Nat/WNat remain the two named instances of the same feature (their predicate
   lives in `refinement_lo`); a general `{v:T|q}` reuses the proof-binder lemma,
   not `refinement_lo`.
3. Generic `'p` at **fn level**: the `'`-binder syntax + the polymorphic-check +
   the contract obligation. **LANDED** (`adsmt-ir-lukb`).
   - **②-A lexer**: a single leading `'` + an identifier (`'p`) lexes as a
     *tick-ident* — a generic predicate parameter (`lexer::is_tick_ident`); it
     lexes back bare (no backtick).
   - **②-B refinement types in type position**: `Type::Refine { var, base, pred }`
     usable in const / fn-param / fn-return (parse/print/round-trip). The
     refinement's *sort* is its base; a `const c: {v:T|φ}` adds the trusted fact
     `φ[v:=c]` as a hypothesis (β-substituted via `subst_top`; dropping it would
     be unsound, as for Nat/WNat free-const positivity). A generic `'p` in a
     const is rejected (no `fn` to bind it).
   - **②-C predicate-polymorphic fns** (`elab.rs::elab_fn`): collect the `'p`
     from every param/return refinement; bind them implicitly at the head as
     `Π('p: base→Prop)` (the body type-checks ONCE with `'p` abstract — the
     "checked-once" guarantee, free from the kernel `Π`). Each param refinement
     is a **precondition**, the return refinement a **postcondition**; the
     contract `∀'p⃗.∀x⃗. (⋀φᵢ) ⟹ ψ(g('p⃗,x⃗))` is a **goal** for a definition (the
     construct-site obligation) and a **trusted axiom** for a signature (the user
     asserts it; use sites instantiate `'p:=q` and discharge the now-monomorphic
     precondition — the dictionary-passing of §5.2). The implication is the CIC
     proof-binder `Π(_:pre). post`, lowering-erased into the relativization
     guard (the §2 path). CONCRETE refinement fns (no `'p`) get the identical
     contract treatment.
   - **Guard algebra (used by `elab_fn`)**: the precondition conjunction is
     structurally **deduped** (idempotence `r ∧ … ∧ r ⟺ r`); the companion
     identities `(p⟹r)∧(q⟹r) ⟺ (p∨q)⟹r` and `(p⟹r)∨(q⟹r) ⟺ (p∧q)⟹r` are the
     simplifications to apply once refinement *combinators* (union/intersection
     of refined domains) land — they keep a merged contract minimal.
   - **Still pending**: the `adsmt-class` predicate-dictionary *registry* (so a
     `'p` resolves through the `Relation`/`Instance`/`Resolver` spine at a use
     site rather than only via the per-fn contract) — the **type-relation-level**
     `'p`, the next phase.
4. z3-differential on concrete refinements + contracts (gated on the lower→solve
   wiring, #325), as for the Nat/WNat collapse.
