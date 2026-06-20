//! complete.rs — THE COMPLETENESS KEYSTONE for the P4 model-completion
//! verdict-flip (the gate stated in `diseq::flip_is_sound`).
//!
//! The flip reads "the conflict search found NO σ with `E_TOT ⊨ (¬ψ)σ`
//! ⇒ `∀x̄.ψ` holds". That is sound only if the search is COMPLETE — every
//! entailed conflict is enumerated, else a missed σ is a spurious sat. The design
//! Workflow flagged a *pruned* search's completeness (`fail_sound` — proving the
//! `R_*`/FAIL eager-prune discards only genuinely-unentailed branches) as
//! research-hard, with no precedent in this crate.
//!
//! **The reframing that makes the keystone tractable.** Completeness is hard only
//! when the search PRUNES. A BRUTE-FORCE enumeration over the FINITE witness
//! domain `dom` (the congruence class representatives of the bound-variable
//! sorts) is complete *by construction*: it visits every candidate tuple, so it
//! cannot miss a witness — there is no `fail_sound` to discharge. The `R_*`/FAIL
//! pruning then becomes a *performance* optimization (P5), verified separately as
//! "pruning preserves the brute-force solution set", NOT a soundness gate. So the
//! flip can be made sound NOW with a brute-force `solve` (slow but provably
//! complete), and sped up later.
//!
//! This module proves the brute-force completeness theorem `solve_complete` and
//! its keystone corollary `no_conflict_when_empty`: if the brute-force search
//! returns ∅, then NO tuple over the witness domain is a conflict — so concluding
//! `Sat` is sound RELATIVE to the domain. The remaining gap — that no conflict
//! exists at a FRESH element outside the finite domain (the infinite-sort case) —
//! is the conservative-extension obligation discharged by the accounting gate
//! (`model_compl.rs` / design §6, Phase 4). Together: domain-completeness here
//! + conservative-extension there ⇒ the full `flip_is_sound`.
use vstd::prelude::*;
use crate::spec::GTerm;

verus! {

/// A substitution σ — the bindings for the bound-variable holes, in order
/// (σ[i] = the ground term bound to hole i).
pub type Tuple = Seq<GTerm>;

/// σ is a length-`holes` tuple drawn from the finite witness domain `dom` (the
/// class representatives of the holes' sorts). Every binding is a real ground
/// term in `dom` — the grounding firewall (invariant (ii)) at the tuple level.
pub open spec fn over_dom(t: Tuple, dom: Seq<GTerm>, holes: nat) -> bool {
    &&& t.len() == holes
    &&& forall|i: int| 0 <= i < t.len() ==> dom.contains(#[trigger] t[i])
}

/// The brute-force solution set: EVERY length-`holes` tuple over `dom` that
/// satisfies the per-σ conflict test `ok`. `ok(σ)` abstracts "`E_TOT ⊨ (¬ψ)σ`"
/// — the conflict check for the constraint `C = ¬ψ`, decided per σ by the
/// congruence `equal`/`disequal` plus the model fold under the defaults `ξ_f`.
/// Because the set is built by COMPREHENSION over all domain tuples, it omits no
/// candidate — this is the brute-force search, exactly.
pub open spec fn solutions(dom: Seq<GTerm>, holes: nat, ok: spec_fn(Tuple) -> bool) -> Set<Tuple> {
    Set::new(|t: Tuple| over_dom(t, dom, holes) && ok(t))
}

/// A conflict exists over the witness domain: some domain tuple passes `ok`.
pub open spec fn conflict_in_domain(dom: Seq<GTerm>, holes: nat, ok: spec_fn(Tuple) -> bool) -> bool {
    exists|t: Tuple| over_dom(t, dom, holes) && #[trigger] ok(t)
}

/// THE COMPLETENESS THEOREM (brute-force form). Every domain tuple that IS a
/// conflict is in the brute-force solution set — the search misses no witness.
/// This is the dual of `diseq::r_yield_sound` (which is "no FALSE solution");
/// together they pin `solve` to EXACTLY the domain conflicts. Trivial by
/// construction precisely because brute-force prunes nothing — which is the whole
/// point of preferring it over a pruned search whose completeness (`fail_sound`)
/// is research-hard.
pub proof fn solve_complete(dom: Seq<GTerm>, holes: nat, ok: spec_fn(Tuple) -> bool, sigma: Tuple)
    requires
        over_dom(sigma, dom, holes),
        ok(sigma),
    ensures
        solutions(dom, holes, ok).contains(sigma),
{
    assert(solutions(dom, holes, ok).contains(sigma) == (over_dom(sigma, dom, holes) && ok(sigma)));
}

/// THE KEYSTONE COROLLARY — the flip's soundness over the witness domain. If the
/// brute-force search returned ∅, then NO domain tuple is a conflict. So the flip
/// concluding `Sat` ("no conflict") is sound relative to the witness domain. This
/// DISCHARGES `diseq::flip_is_sound`'s finite-domain obligation (the part that
/// does not depend on fresh elements). The infinite-sort extension is the
/// conservative-extension proof (Phase 4).
pub proof fn no_conflict_when_empty(
    dom: Seq<GTerm>,
    holes: nat,
    ok: spec_fn(Tuple) -> bool,
)
    requires
        solutions(dom, holes, ok) =~= Set::<Tuple>::empty(),
    ensures
        !conflict_in_domain(dom, holes, ok),
{
    assert forall|t: Tuple| over_dom(t, dom, holes) implies !ok(t) by {
        if ok(t) {
            solve_complete(dom, holes, ok, t);
            // t ∈ solutions, but solutions = ∅ — contradiction.
            assert(solutions(dom, holes, ok).contains(t));
            assert(Set::<Tuple>::empty().contains(t));
        }
    }
}

/// The contrapositive, stated as the flip's GUARD: a conflict in the domain
/// implies the brute-force search is non-empty (so the flip will NOT wrongly
/// conclude `Sat`). The implementation reads `solutions.is_empty()` to decide the
/// flip; this is why that read is sound.
pub proof fn conflict_implies_nonempty(
    dom: Seq<GTerm>,
    holes: nat,
    ok: spec_fn(Tuple) -> bool,
)
    requires
        conflict_in_domain(dom, holes, ok),
    ensures
        !(solutions(dom, holes, ok) =~= Set::<Tuple>::empty()),
{
    let sigma = choose|t: Tuple| over_dom(t, dom, holes) && ok(t);
    solve_complete(dom, holes, ok, sigma);
    assert(solutions(dom, holes, ok).contains(sigma));
}

} // verus!
