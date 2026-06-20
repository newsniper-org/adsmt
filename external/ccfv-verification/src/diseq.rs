//! Disequality entailment + the `R_*` rule soundness (the disequality dual of
//! `spec::yield_sound`) — the `[선검증]` substrate for the complete E-ground
//! (dis)unification core that the P4 model-completion verdict-flip needs.
//!
//! `spec.rs` proved the EQUALITY half: an `Interp` (a coloring of ground terms)
//! models a context of equalities, and a YIELD is sound when the context entails
//! every equality literal. Here we add the DISEQUALITY half. A context now also
//! carries *disequalities* (`neqs`): a model must give the two sides DIFFERENT
//! colors. The disequality dual of entailment is `entails_diseq` — every model of
//! the context separates `s` and `t` — and the `R_VAR/R_FAPP/R_GEN` rules are
//! SOUND exactly when each yielded `s ≄ t` is `entails_diseq`-entailed.
//!
//! This file is intentionally SELF-CONTAINED over a richer context `DCtx{eqs,
//! neqs}`, so it does NOT ripple through the eq-only lemmas of `spec.rs`/
//! `congruence.rs`/`capstone.rs` (which stay verified as-is).
//!
//! What is proved here (the SOUNDNESS direction — "no false YIELD"):
//!   * `entails_diseq_member` — an asserted `s ≄ t` is entailed;
//!   * `entails_diseq_sym` — disequality is symmetric;
//!   * `entails_diseq_mono` — growing the context never loses a disequality
//!     entailment (so the search accumulating `E_σ` stays sound);
//!   * `r_yield_sound` — THE disequality YIELD-soundness theorem: if every
//!     (dis)equality literal of a closed branch is entailed, every model of the
//!     context satisfies the whole branch — the firewall stays sound with the
//!     disequality rules added.
//!
//! What is the GATE (the COMPLETENESS direction — "no MISSED YIELD"), stated but
//! NOT discharged here: `solve_diseq_complete` — the model-completion verdict-flip
//! reads "no σ found ⇒ ∀ holds", so it additionally needs that the search
//! enumerates EVERY entailed σ. That is a strictly harder, model-exhibiting proof
//! (`complete.rs`) and is the documented precondition for ACTIVATING the flip; the
//! flip stays disabled until it discharges. See the crate docs + design §6/§8.
use vstd::prelude::*;
use crate::spec::{GTerm, Interp};

verus! {

/// A (dis)equality literal `s ⋈ t` (the relation is fixed by where it is stored
/// — `DCtx.eqs` vs `DCtx.neqs`).
pub struct Pair {
    pub s: GTerm,
    pub t: GTerm,
}

/// A context with BOTH equalities and disequalities — `E ∪ E_σ` once the search
/// also accumulates disequality bindings. (EUF congruence-closes the equalities;
/// the disequalities are the asserted `≄` plus, on the total view `E_TOT`, the
/// all-pairs separation among distinct class reps.)
pub struct DCtx {
    pub eqs: Set<Pair>,
    pub neqs: Set<Pair>,
}

/// `a` models `ctx`: every equality holds (same color) AND every disequality
/// holds (different color). A coloring is automatically an equivalence relation,
/// so this is the model-theoretic stand-in for a congruence extended with
/// disequalities.
pub open spec fn dmodels(a: Interp, ctx: DCtx) -> bool {
    (forall|e: Pair| #[trigger] ctx.eqs.contains(e) ==> a(e.s) == a(e.t))
        && (forall|e: Pair| #[trigger] ctx.neqs.contains(e) ==> a(e.s) != a(e.t))
}

/// `E ∪ E_σ ⊨ s ≃ t` (equality entailment over the richer context).
pub open spec fn dentails_eq(ctx: DCtx, s: GTerm, t: GTerm) -> bool {
    forall|a: Interp| dmodels(a, ctx) ==> a(s) == a(t)
}

/// `E ∪ E_σ ⊨ s ≄ t` — every model of the context gives `s` and `t` different
/// colors. This is exactly the guard an `R_*` rule must satisfy before closing a
/// branch on a disequality literal (the dual of `spec::entails`).
pub open spec fn entails_diseq(ctx: DCtx, s: GTerm, t: GTerm) -> bool {
    forall|a: Interp| dmodels(a, ctx) ==> a(s) != a(t)
}

/// Membership: an asserted disequality is entailed (the `R_VAR` base case — a
/// hole bound to a term provably apart from the other side).
pub proof fn entails_diseq_member(ctx: DCtx, p: Pair)
    requires
        ctx.neqs.contains(p),
    ensures
        entails_diseq(ctx, p.s, p.t),
{
    assert forall|a: Interp| #![auto] dmodels(a, ctx) implies a(p.s) != a(p.t) by {
        assert(ctx.neqs.contains(p));
    }
}

/// Disequality is symmetric.
pub proof fn entails_diseq_sym(ctx: DCtx, x: GTerm, y: GTerm)
    requires
        entails_diseq(ctx, x, y),
    ensures
        entails_diseq(ctx, y, x),
{
    assert forall|a: Interp| #![auto] dmodels(a, ctx) implies a(y) != a(x) by {
        assert(a(x) != a(y));
    }
}

/// `s ≄ t` plus `t ≃ u` (a congruence merge) gives `s ≄ u` — the disequality
/// propagation an `R_FAPP` step uses when an argument class is merged.
pub proof fn entails_diseq_cong(ctx: DCtx, s: GTerm, t: GTerm, u: GTerm)
    requires
        entails_diseq(ctx, s, t),
        dentails_eq(ctx, t, u),
    ensures
        entails_diseq(ctx, s, u),
{
    assert forall|a: Interp| #![auto] dmodels(a, ctx) implies a(s) != a(u) by {
        assert(a(s) != a(t));
        assert(a(t) == a(u));
    }
}

/// Monotonicity: growing the context (the search extending `E_σ` with more
/// equalities AND disequalities) never loses a disequality entailment. This is
/// why `R_*` extending `E_σ` preserves soundness, exactly as `entails_mono` does
/// for the equality rules.
pub proof fn entails_diseq_mono(c1: DCtx, c2: DCtx, x: GTerm, y: GTerm)
    requires
        c1.eqs.subset_of(c2.eqs),
        c1.neqs.subset_of(c2.neqs),
        entails_diseq(c1, x, y),
    ensures
        entails_diseq(c2, x, y),
{
    assert forall|a: Interp| #![auto] dmodels(a, c2) implies a(x) != a(y) by {
        assert forall|e: Pair| #![auto] c1.eqs.contains(e) implies a(e.s) == a(e.t) by {
            assert(c2.eqs.contains(e));
        }
        assert forall|e: Pair| #![auto] c1.neqs.contains(e) implies a(e.s) != a(e.t) by {
            assert(c2.neqs.contains(e));
        }
        assert(dmodels(a, c1));
    }
}

// ----- THE disequality YIELD-soundness theorem (dual of spec::yield_sound) -----

/// A closed branch's literals: the equalities it must entail and the
/// disequalities it must entail (`Cσ` split by relation).
pub open spec fn branch_entailed(ctx: DCtx, eqs: Set<Pair>, neqs: Set<Pair>) -> bool {
    (forall|e: Pair| #[trigger] eqs.contains(e) ==> dentails_eq(ctx, e.s, e.t))
        && (forall|e: Pair| #[trigger] neqs.contains(e) ==> entails_diseq(ctx, e.s, e.t))
}

/// THE DISEQUALITY YIELD-SOUNDNESS THEOREM. If a closed branch's guard holds —
/// every equality literal is `dentails_eq`-entailed AND every disequality literal
/// is `entails_diseq`-entailed by `E ∪ E_σ` — then every model of `E ∪ E_σ`
/// satisfies the WHOLE branch (all its (dis)equalities). So the complete CCFV
/// (matching half + the `R_*` disequality rules) never closes a branch the model
/// refutes: the never-conclude-unsat firewall stays sound with disequalities
/// added as a candidate source.
pub proof fn r_yield_sound(ctx: DCtx, eqs: Set<Pair>, neqs: Set<Pair>)
    requires
        branch_entailed(ctx, eqs, neqs),
    ensures
        forall|a: Interp|
            dmodels(a, ctx) ==> ((forall|e: Pair| #[trigger] eqs.contains(e) ==> a(e.s) == a(e.t))
                && (forall|e: Pair| #[trigger] neqs.contains(e) ==> a(e.s) != a(e.t))),
{
    assert forall|a: Interp| dmodels(a, ctx) implies ((forall|e: Pair|
        #[trigger] eqs.contains(e) ==> a(e.s) == a(e.t)) && (forall|e: Pair|
        #[trigger] neqs.contains(e) ==> a(e.s) != a(e.t))) by {
        assert forall|e: Pair| eqs.contains(e) implies a(e.s) == a(e.t) by {
            assert(dentails_eq(ctx, e.s, e.t));
        }
        assert forall|e: Pair| neqs.contains(e) implies a(e.s) != a(e.t) by {
            assert(entails_diseq(ctx, e.s, e.t));
        }
    }
}

// ----- THE COMPLETENESS GATE (stated, NOT discharged here — see complete.rs) ---

/// THE GATE for the model-completion verdict-flip. The flip reads "the search
/// found NO σ with `E_TOT ⊨ (¬ψ)σ` ⇒ `∀x̄.ψ` holds in `E_TOT`". That is sound
/// ONLY IF the search is COMPLETE: every entailed conflict σ is enumerated, i.e.
///
///   `(∃a. dmodels(a, E_TOT) ∧ a-refutes-ψ-at-σ)  ⇒  σ ∈ search.enumerated`.
///
/// This is the DUAL of `r_yield_sound` (which is "no FALSE yield"); completeness
/// is "no MISSED yield" and is a strictly harder, model-exhibiting proof. It is
/// NOT proved in this module — it is the documented precondition gating
/// activation of the flip (the `ccfv_model_compl` flag stays OFF until
/// `complete.rs` discharges it). Stated here as the explicit obligation so the
/// gate is visible in the verified surface.
pub open spec fn flip_is_sound(
    e_tot: DCtx,
    enumerated: Set<Pair>,
    conflict_exists: bool,
) -> bool {
    // The flip concludes `∀ holds` (returns Some(true)) exactly when the search
    // enumerated nothing. `flip_is_sound` says: whenever it so concludes, there
    // really is no conflict. Discharging it requires the completeness lemma.
    (enumerated =~= Set::<Pair>::empty()) ==> !conflict_exists
}

} // verus!
