//! model_compl.rs — Phase 4: the CONSERVATIVE-EXTENSION / fresh-element half of
//! the P4 model-completion verdict-flip's soundness.
//!
//! `complete.rs` proved the DOMAIN half: the brute-force search over the finite
//! witness domain (the class reps of the bound-variable sorts) is complete by
//! construction, so "search returned ∅ ⇒ no conflict over the witness domain"
//! (`no_conflict_when_empty`). That leaves exactly one gap, flagged there and in
//! `diseq::flip_is_sound`: the witness domain is FINITE, but an uninterpreted sort
//! is INFINITE — could a conflict hide at a FRESH element outside the domain, so
//! the flip's `Sat` is spurious?
//!
//! This module proves it cannot, for the fragment the flip is restricted to (pure
//! uninterpreted-sort E-(dis)unification). The argument is the design's §6
//! conservative extension: a fresh element `e` — one the context `E ∪ E_σ`
//! mentions in NO literal — is entailed neither equal nor disequal to any other
//! term. So no (dis)equality literal about a fresh application is entailed, hence
//! the conflict `E_TOT ⊨ (¬ψ)σ` cannot hold at a σ that binds a fresh element:
//! the search misses no conflict by stopping at the finite domain.
//!
//! The model-theoretic mechanism is RECOLORING. Given any model `a` of the
//! context, recoloring a fresh term `e` to any color `k` yields another model
//! (the context mentions `e` nowhere, so no literal's truth changes). Hence `e`'s
//! color is FREE — it can be made to match the other side (refuting a would-be
//! disequality conflict) or to differ from it (refuting a would-be equality
//! conflict). That free choice is exactly the completion's freedom on
//! under-specified applications (`ξ_f`), and the accounting gate (`model_compl`'s
//! `body_symbols_accounted`) is what guarantees the fresh element really is
//! mentioned nowhere — i.e. that `fresh_for` holds.
//!
//! Self-contained over `diseq`'s richer `DCtx{eqs, neqs}` (the same context the
//! disequality YIELD-soundness uses), so it ripples through nothing already
//! verified. Together: `complete::no_conflict_when_empty` (domain) +
//! `fresh_imposes_no_conflict` (fresh) ⇒ the full `diseq::flip_is_sound` over the
//! whole infinite sort.
use vstd::prelude::*;
use crate::spec::{GTerm, Interp};
use crate::diseq::{DCtx, Pair, dmodels, dentails_eq, entails_diseq};

verus! {

/// `e` is FRESH for `ctx`: it occurs in no (dis)equality literal. This is the
/// model-theoretic shadow of the accounting gate — a bound-variable binding (and
/// the completion-target applications over it) that the asserted formula never
/// constrains, so the completion is free to color it.
pub open spec fn fresh_for(ctx: DCtx, e: GTerm) -> bool {
    &&& (forall|p: Pair| #[trigger] ctx.eqs.contains(p) ==> p.s != e && p.t != e)
    &&& (forall|p: Pair| #[trigger] ctx.neqs.contains(p) ==> p.s != e && p.t != e)
}

/// The interpretation `a` recolored to give `e` the color `k` (and every other
/// term its old color). The witness the freshness proofs exhibit.
pub open spec fn recolor(a: Interp, e: GTerm, k: int) -> Interp {
    |x: GTerm| if x == e { k } else { a(x) }
}

/// THE CORE LEMMA. Recoloring a FRESH term preserves modeling: if `a` models
/// `ctx` and `e` occurs in no literal of `ctx`, then `a` recolored at `e` (to any
/// color) still models `ctx`. Because every literal's two sides differ from `e`,
/// the recolor changes neither side's color, so every equality/disequality keeps
/// its truth. This is the conservative-extension primitive — the completion may
/// assign a fresh application any value without disturbing the asserted facts.
pub proof fn recolor_preserves_dmodels(a: Interp, ctx: DCtx, e: GTerm, k: int)
    requires
        fresh_for(ctx, e),
        dmodels(a, ctx),
    ensures
        dmodels(recolor(a, e, k), ctx),
{
    let a2 = recolor(a, e, k);
    assert forall|p: Pair| #[trigger] ctx.eqs.contains(p) implies a2(p.s) == a2(p.t) by {
        assert(p.s != e && p.t != e);  // freshness
        assert(a2(p.s) == a(p.s) && a2(p.t) == a(p.t));
        assert(a(p.s) == a(p.t));  // a models ctx
    }
    assert forall|p: Pair| #[trigger] ctx.neqs.contains(p) implies a2(p.s) != a2(p.t) by {
        assert(p.s != e && p.t != e);
        assert(a2(p.s) == a(p.s) && a2(p.t) == a(p.t));
        assert(a(p.s) != a(p.t));
    }
}

/// A fresh element is entailed DISEQUAL to nothing (distinct) — there is a model
/// of `ctx` that colors `e` and `t` the SAME, so `E ∪ E_σ ⊭ e ≄ t`. Refutes the
/// disequality-conflict at a fresh binding: a `¬ψ` cube literal `e ≄ t` is never
/// entailed, so it cannot close a conflict branch on a fresh element.
pub proof fn fresh_not_entailed_diseq(a: Interp, ctx: DCtx, e: GTerm, t: GTerm)
    requires
        dmodels(a, ctx),
        fresh_for(ctx, e),
        e != t,
    ensures
        !entails_diseq(ctx, e, t),
{
    // Recolor `e` to share `t`'s color; still a model (e fresh), and now e ≃ t.
    let a2 = recolor(a, e, a(t));
    recolor_preserves_dmodels(a, ctx, e, a(t));
    assert(a2(e) == a(t));
    assert(a2(t) == a(t));  // t != e, so recolor leaves t untouched
    assert(a2(e) == a2(t));
    // a2 is a model of ctx with a2(e) == a2(t), so the universal in entails_diseq fails.
    assert(dmodels(a2, ctx) && a2(e) == a2(t));
}

/// A fresh element is entailed EQUAL to nothing (distinct) — there is a model of
/// `ctx` that colors `e` and `t` DIFFERENTLY, so `E ∪ E_σ ⊭ e ≃ t`. Refutes the
/// equality-conflict at a fresh binding: a `¬ψ` cube literal `e ≃ t` is never
/// entailed. (Colors are `int`, so `a(t) + 1` is a color distinct from `a(t)` —
/// the fresh element always has an unused color available, the infinite-sort
/// witness.)
pub proof fn fresh_not_entailed_eq(a: Interp, ctx: DCtx, e: GTerm, t: GTerm)
    requires
        dmodels(a, ctx),
        fresh_for(ctx, e),
        e != t,
    ensures
        !dentails_eq(ctx, e, t),
{
    let a2 = recolor(a, e, a(t) + 1);
    recolor_preserves_dmodels(a, ctx, e, a(t) + 1);
    assert(a2(e) == a(t) + 1);
    assert(a2(t) == a(t));  // t != e
    assert(a2(e) != a2(t));
    assert(dmodels(a2, ctx) && a2(e) != a2(t));
}

/// THE CAPSTONE — a fresh element imposes NO conflict. For a fresh `e` and any
/// distinct `t`, the context entails NEITHER `e ≃ t` NOR `e ≄ t`. So whichever
/// relation a `¬ψ` cube needs at a binding to a fresh element, it is unentailed:
/// the conflict `E_TOT ⊨ (¬ψ)σ` fails for any σ that binds a fresh element. This
/// is the fresh-element half of the flip's soundness — combined with
/// `complete::no_conflict_when_empty` (the search exhausts the finite witness
/// domain), the flip's "search empty ⇒ `Sat`" is sound over the WHOLE infinite
/// uninterpreted sort, not merely the enumerated reps: a fresh witness can never
/// turn an enumerated-no-conflict into a real one. This discharges the
/// conservative-extension obligation that `complete.rs` left open and
/// `diseq::flip_is_sound` named.
pub proof fn fresh_imposes_no_conflict(a: Interp, ctx: DCtx, e: GTerm, t: GTerm)
    requires
        dmodels(a, ctx),
        fresh_for(ctx, e),
        e != t,
    ensures
        !dentails_eq(ctx, e, t),
        !entails_diseq(ctx, e, t),
{
    fresh_not_entailed_eq(a, ctx, e, t);
    fresh_not_entailed_diseq(a, ctx, e, t);
}

} // verus!
