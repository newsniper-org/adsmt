# Term-level `ite` lowering (fresh-var-free atom duplication)

## Problem

`adsmt-ir-lower` lowers a Bool-branch `ite` (`ite : Π(A:Type). Prop → A → A → A`
with `A = Bool/Prop`) to `(c → t) ∧ (¬c → e)`. A **term-level** `ite` — one whose
result sort `A` is `Int`/`Real`/an uninterpreted sort — abstains
(`lower.rs`: *"ite over a non-Bool sort (the solver has no ite term)"*), because
`adsmt-core` has **no `Ite` term** (it has no term-level conditional). Verus emits
term-`ite` pervasively (`if`-expressions in specs), so this abstain turns a large
class of otherwise-first-order obligations into the sound-but-useless `Unknown`.

## Why not fresh-var lifting

The textbook lift — introduce a fresh `v:A`, replace the `ite` with `v`, and add
the definition `(c → v=t) ∧ (¬c → v=e)` — is **not** a good fit for this lowering:

1. **Binder capture.** An `ite` under a quantifier — `∀x. … ite(c[x], t[x], e[x]) …`
   — needs `v` to depend on `x` (a Skolem *function* `v(x)`, not a variable), and
   its definition must live **inside** the quantifier body. The existing side-hyp
   channel (`Lowerer::extra_hyps`) is a **flat, top-level** list; a definition
   dropped there would leave `x` free (unsound / ill-formed).
2. **Goal/hyp polarity.** `extra_hyps` is drained into the `Lowered::goals` list,
   and the lu-kb driver **negates each goal**. A `v`-definition appended there
   would be negated — wrong. (It is correct only for the Nat/WNat *positivity*
   hyps, which are true facts on free constants, and even those only for the
   hypothesis-lowering direction.)

## The transform: atom duplication

Rewrite the smallest enclosing **formula** `F` that contains the term-`ite` in a
term position:

```
F[ite(c, a, b)]   ⟿   (c → F[a]) ∧ (¬c → F[b])
```

where `F[a]` / `F[b]` replace the chosen `ite` occurrence by its `then` / `else`
branch. `c` is `Prop`-sorted (already a formula), so it is used directly as the
guard; `a`, `b` are the branch terms.

This is **satisfiability-preserving** because it is a *semantic equivalence*:
given `ite(c,a,b) = (if c then a else b)`, in every model `M`,
`M ⊨ F[ite(c,a,b)] ⟺ M ⊨ (c → F[a]) ∧ (¬c → F[b])` (case split on `M ⊨ c`).
Two properties fall out of this being an equivalence, and they are exactly the two
hazards the fresh-var route hits:

- **Capture-free.** No fresh symbol is introduced; `c`, `a`, `b` stay at their
  original de-Bruijn depth (the rewrite is applied *in place*, at the same binder
  level), so nothing is captured and no index is shifted. Under `∀x`, the rewrite
  is applied to the body, keeping `c[x]` in scope: `∀x. (c[x]→G[a])∧(¬c[x]→G[b])`.
- **Polarity-free.** Because `F ⟺ F'`, replacing `F` by `F'` is valid whether `F`
  occurs positively or negatively — no side-channel, no goal/hyp distinction.

### Where the rewrite is applied

The rewrite is valid at *any* enclosing `Prop` node, but is applied at the
**smallest** one (the atom, or the innermost quantifier body containing the ite)
to minimise duplication. Concretely, during `lower_term`, when about to lower a
Bool-sorted **atom** (comparison / equality / predicate application) whose
argument terms contain a term-`ite`, hoist the **innermost** such `ite` to the
atom and recurse. "Innermost" (a, b, c themselves `ite`-free at term level) makes
the measure `Σ_atoms (2^(#ites in atom) − 1)` strictly decrease per step, so the
rewrite terminates (a single atom with `k` ites expands to ≤ `2^k` ite-free
atoms).

## Soundness (pre-verified)

`~/term-ite-lifting-verification/src/ite_lift.rs` (Verus) proves, over a modelled
term/formula AST with a de-Bruijn environment `eval`:

1. **`eval_ite`** — `eval_term(env, Ite(c,a,b)) = if eval_form(env,c) {eval_term(env,a)} else {eval_term(env,b)}` (definitional).
2. **`term_subst_cong`** — replacing a subterm `s` by `s'` with `eval_term(env,s)=eval_term(env,s')` preserves `eval_term(env, ·)` (handles an `ite` nested inside `Add(ite, k)`; no binders inside terms).
3. **`atom_lift_equiv`** — `eval_form(env, F[ite]) = eval_form(env, (c→F[a]) ∧ (¬c→F[b]))` for all `env` (the core; case split on `eval_form(env,c)`, using 1+2).
4. **`rewrite_subformula_preserves`** — replacing a subformula `G` by `G'` with `∀env. eval_form(env,G)=eval_form(env,G')` preserves the whole formula's truth, by structural induction **through the quantifier binders** (this is what licenses applying the local rewrite anywhere in the tree, including under `∀`/`∃`).

3+4 together: the transform is satisfiability-preserving in **both** directions
(no false-sat, no false-unsat).

## Scope of this slice

- Term-`ite` over any first-order sort (`Int`/`Real`/uninterpreted), at top level
  and **under quantifiers** (the atom-duplication handles both uniformly).
- Nested / multiple ites in one atom (innermost-first expansion).
- Out of scope (unchanged abstains): the Bool-`ite` path (already lowered), and
  anything the enclosing atom itself cannot lower (higher-order, recursion).

## The `let`-blocked extension (#403 corpus residual)

The hoist's ite search walks only the atom's binder-free skeleton (application
spines + ite branches), so a `let` node hides any ite inside it — and the verus
fuel definitions produce exactly that shape (`let p = sel(x) in ite(p < 10, …)`
inside a data-valued ite branch). By the time the ordinary recursion ζ-reduces
the `let` at head position (`whnf`), the enclosing atom is gone and the revealed
non-Bool ite has no lift site (a sound but avoidable abstain). Fix
(`inline_definitional_redex`): when an atom has NO hoistable ite, ζ/β-inline ONE
ite-carrying definitional redex found on the same skeleton walk — a kernel `Let`
(the lukb face keeps them) or a β-redex `(λx. b) v` (the SMT-LIB face elaborates
`let` that way) — and re-enter; the surfaced ite then hoists normally. The
rewrite is the kernel's own definitional step (`subst_top`, exactly what `whnf`
applies at head position), so it is conversion-sound and needs no new
verification lemma; termination is the strong normalization of kernel ζ/β plus
the unchanged hoist measure. A redex with no `ite` inside is skipped (it
head-reduces on the normal path; inlining it would only force a wasted atom
re-descent).
