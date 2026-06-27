# `solve … by …` — in-language proof obligations as proof terms (semantics B)

**Status:** design (2026-06-27). Supersedes the `Preserving('p)` type-relation
attempt (retired, commit `fa7deca`). See
`docs/design/REFINEMENT_TYPES_AND_GENERIC_CONSTRAINTS.md`,
`[[feedback-preservation-is-higher-order-predicate]]`.

## 1. Motivation

Predicate **preservation** is a property of a *function*, not of a type (a type
relation is coherent — one instance per type — but a datatype `A` can have many
`'p`-preserving functions). So it is a **higher-order predicate** `preserving(f)`,
each function checked independently. The natural way to *express and discharge*
such a property in the surface is an in-language proof construct:

```
fn preserving(f: {u: A | 'p(u)} -> {v: A | 'q(v)}) -> Bool:
    let result = solve forall {x: A | 'p(x)}. 'p(f(x))
                 by:   forall {y = f(x) | 'p(x)}. 'q(y) ==> 'p(y)
    return result
```

`solve G by L` is the building block: it **proves** `G`, citing the lemma `L`.
The chosen semantics is **(B) proof-term construction** — `solve G by L`
elaborates to a *kernel-checked proof term* of `G`; there is NO runtime call to
the solver in the value world. The kernel verifies the proof skeleton; the engine
discharges the leaf obligation(s). Pure, and inside the kernel firewall.

## 2. Refinement function types

A refined arrow `{u:A | 'p(u)} -> {v:A | 'q(v)}` is, in CIC:

```
Π(u:A). 'p(u) → Σ(v:A). 'q(v)          -- proof-relevant reading
```

but adsmt's lukb elaboration is **proof-irrelevant** (proofs erased at lowering;
see ②-C). So lukb elaborates a refined-arrow parameter `f` to its **value arrow**
plus its **postcondition contract** as an available hypothesis in the body scope:

```
f : Π(u:A). A                                   -- value level ('p proof erased)
post_f : ∀(x:A). 'p(x) ⟹ 'q(f(x))              -- f's codomain refinement, a FACT
```

`post_f` is exactly what f's *type* asserts (a refined codomain is a postcondition
— the ② contract, here flowing the OTHER way: a refined-arrow *argument* GIVES its
postcondition as a usable fact, rather than generating it as an obligation). The
domain refinement `'p(u)` is the precondition: a use `f(x)` is only well-formed
where `'p(x)` is in scope.

## 3. `solve G by L` — the cut / lemma-introduction rule

`solve G by L` is the structured-proof **cut**: "to prove `G`, it suffices to
establish the lemma `L`; here is `L`." It elaborates to two obligations and a
proof term:

```
solve G by L   ⤳   let pf_L : L = ⟨obligation L⟩                  -- the leaf
                   let pf_G : G = ⟨obligation G, with L in scope⟩  -- the bridge
                   pf_G
```

- **Leaf** `L` — the genuine content (for `preserving`: `'q ⟹ 'p` on the image).
  Discharged by the engine; a certificate is kernel-checked.
- **Bridge** `G` *under* the hypothesis `L` (and the ambient facts, e.g. `post_f`)
  — usually trivial/structural (a modus-ponens step). Discharged the same way.
- `result : G` is the composed, kernel-checked proof.

**Soundness = the cut rule**, which is unconditionally sound: if `⊢ L` and
`L ⊢ G` then `⊢ G`. The construct adds NO axiom and NO verdict write-path — both
`L` and `G`-under-`L` are real obligations checked by the engine + kernel; `by L`
only *structures* the proof (and lets the user name the key lemma so the system
need not guess the intermediate). If either obligation is unprovable,
`solve G by L` fails to verify — i.e., `preserving(f)` is rejected at check time
for an `f` whose `'q` does not imply `'p`.

## 4. The `preserving` example, fully

With `f : {u:A|'p} -> {v:A|'q}` (so `post_f : ∀x. 'p(x) ⟹ 'q(f(x))`):

```
G  =  ∀(x:A). 'p(x) ⟹ 'p(f(x))
L  =  ∀(x:A). 'p(x) ⟹ ('q(f(x)) ⟹ 'p(f(x)))      -- 'q⟹'p on the image
```

The **bridge** proof term (kernel-checkable, pure CIC):

```
pf_G  =  λ(x:A). λ(hp : 'p(x)).
            (pf_L x hp) (post_f x hp)            : 'p(f(x))
         -- pf_L x hp : 'q(f(x)) ⟹ 'p(f(x))
         -- post_f x hp : 'q(f(x))
```

So `G ⟸ (post_f ∧ L)` is a *closed kernel proof term* — no engine needed for the
bridge. The ONLY engine leaf is `L`. That is the payoff of (B): the kernel builds
the scaffold; the solver fills exactly one hole.

`preserving` therefore has the dependent type
`Π(f: {u:A|'p}->{v:A|'q}). (∀x. 'p(x) ⟹ 'p(f(x)))` — given any such `f`, it
*produces a proof* that `f` preserves `'p` (valid iff the `L` leaf discharges).
The surface `-> Bool` is loose for this proof-of-a-Prop return.

## 5. lukb surface + elaboration

New surface:
- **Refined arrow types** in parameter/return position: `{u:A|'p} -> {v:A|'q}`
  (the arrow type does not yet exist in `ast::Type`; add `Type::Arrow` carrying
  refined domain/codomain, or desugar at parse).
- **`solve <G-block> by <L-block>`** as a term form (a new
  `Term::SolveBy(g_block, l_block)`), elaborating per §3.

**G and L are each a BLOCK, not a single term** (user, 2026-06-27). A block is a
sequence that may bind intermediate results with `let` (and other structured
forms) and ends in the proposition it denotes — e.g.
`solve (let a = …; let b = …; <goal-prop>) by (let c = …; <lemma-prop>)`. A block
elaborates to its final Prop with the `let`s folded in (lukb already has
`let x = e in body`; a block is the layout/`;`-form of a `let`-chain). So G/L
denote Props exactly as in §3–§4; the block form only adds local naming inside
each.

**Inference-sugar binders (user, 2026-06-27).** The surface
`forall {y = f(x) | 'p(x)}. φ` is a HEAVILY ABBREVIATED, type-inference-driven
form — NOT a naïve refinement binder. It introduces the **preimage** `x`
(inferred `x:A` from `f`'s domain), constrains it by `'p(x)`, and binds the
**image** `y = f(x)` (a `let`). It desugars to
`forall x: {A | 'p(x)}. let y = f(x) in φ`  ≡  (with `y` unfolded)
`forall x: {A | 'p}. φ[y := f(x)]`. So the example's `L` is exactly §4's
`∀x:{A|'p}. 'q(f(x)) ⟹ 'p(f(x))`. The elaborator must run inference to recover
`x`'s sort + the `y = …` definitional binding; it must NOT treat `{y = f(x) | …}`
as the `{v:T | φ}` refinement-type binder of ①.

Elaboration of `solve G by L` in `elab_term`:
1. elaborate the `G`/`L` **blocks** to kernel Props (folding their `let`s),
   in the ambient ctx (which carries `post_f` etc.), running inference for the
   sugar binders above.
2. construct the bridge proof term `pf_G` parameterised by `pf_L : L` and the
   in-scope facts (for the general case the bridge is itself an obligation
   `(ctx ∧ L) ⟹ G`; for the structural `preserving` shape it is the explicit term
   of §4 — slice 1 may emit the bridge as an obligation and specialise later).
3. push `L` and the bridge as obligations (goals), thread `pf_G : G` as the value.

The `Elaborated.goals` gains the leaf `L` and the bridge; the function's body
value is the proof term. (lukb's existing model — bodies are δ-definitions,
obligations are goals — extends cleanly: `solve/by` adds goals + yields a proof.)

## 6. Soundness invariants + pre-verification (선검증)

Invariants:
- (cut) `solve G by L` NEVER asserts `G` without both `L` and `G`-under-`L`
  reaching the obligation set. No `by` may shortcut an obligation (cf. the
  opaque-fallback soundness rule).
- (firewall) the bridge proof term is kernel-`infer`-checked at type `G`; a bogus
  bridge is rejected by the kernel, never trusted.
- (erasure) the refined-arrow postcondition `post_f` is a real hypothesis derived
  from f's *type*, not an unproven assumption — sound because supplying `f` at a
  refined-arrow type already obligated f's definer to establish it (the ② contract).

**선검증 LANDED** (`~/solve-by-verification`, `verus src/solve_by.rs` → **5
verified, 0 errors**). Over uninterpreted `spec_fn` predicates/function (holds for
every model): `cut` (the `solve G by L` cut is unconditionally sound),
`preserving_bridge` / `preserving_solve_by` (the §4 closed bridge
`(post_f ∧ L) ⟹ G` = the modus-ponens term `pf_G = λx hp. (pf_L x hp)(post_f x hp)`),
and `image_quantifier_desugar` (the inference-sugar binder `∀{y=f(x)|'p}. φ(y)`
≡ the preimage form `∀x. p(x) ⟹ φ(f(x))`). This gates the lukb implementation.

## 7. Phasing

1. **This doc** + 선검증 of the cut + the inference-sugar desugar. **DONE**
   (`~/solve-by-verification`, 5 verified, 0 errors).
2. lukb `Type::Arrow` (refined function types) — parse/elab/print/round-trip.
3. lukb **`solve … by …`** term over **blocks** (§5): the `solve`/`by` clauses are
   `let`-chain blocks; parse/elab to the cut obligations + proof term.
4. The **inference-sugar binders** (§5): `forall {y = f(x) | 'p(x)}. …` →
   `forall x:{A|'p}. let y = f(x) in …`, with type inference recovering `x`'s sort.
5. `preserving` as a library/example higher-order predicate over a refined arrow,
   end-to-end (the §4 bridge), with the leaf `L` discharged by the engine.
