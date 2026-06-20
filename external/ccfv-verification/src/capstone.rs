//! Capstone: the firewall property CCFV must give the clean-MBQI engine — a
//! yielded instantiation is **both** sound (its literals are entailed by
//! `E ∪ E_σ`) **and** grounded (every bound variable maps into `T(E)`). Together
//! with termination (`terminate`), these are exactly the three obligations the
//! never-conclude-unsat firewall and the inner search rest on (design §6 / §12).
use vstd::prelude::*;
use crate::spec::{EqLit, GTerm, Interp, clause_entailed, holds, models};
use crate::ground::{EVar, Subst, grounded, partial_grounded};

verus! {

/// A CCFV YIELD is *admissible* when both firewall preconditions hold at the
/// branch it closes: the partial solution is grounded (every binding so far is in
/// `T(E)`) and every bound variable of the clause has been assigned.
pub open spec fn yield_admissible(
    sigma: Subst,
    bvars: Set<EVar>,
    universe: Set<GTerm>,
    ctx: Set<EqLit>,
    cl: Set<EqLit>,
) -> bool {
    &&& partial_grounded(sigma, universe)
    &&& (forall|v: EVar| #[trigger] bvars.contains(v) ==> sigma.dom().contains(v))
    &&& clause_entailed(ctx, cl)
}

/// THE FIREWALL THEOREM. An admissible YIELD produces an instantiation that is
/// BOTH grounded into `T(E)` (so it passes the `instantiate` gate by construction
/// — no fabricated witness) AND sound (every model of `E ∪ E_σ` satisfies all of
/// `Cσ` — so the engine can never `emit` a binding the model refutes). This is the
/// pair of properties that keeps clean-MBQI's never-conclude-unsat firewall intact
/// when CCFV becomes the unified candidate source.
pub proof fn admissible_yield_is_grounded_and_sound(
    sigma: Subst,
    bvars: Set<EVar>,
    universe: Set<GTerm>,
    ctx: Set<EqLit>,
    cl: Set<EqLit>,
)
    requires
        yield_admissible(sigma, bvars, universe, ctx, cl),
    ensures
        // (ii) grounding
        grounded(sigma, bvars, universe),
        // (i) soundness
        forall|a: Interp|
            models(a, ctx) ==> (forall|e: EqLit| #[trigger] cl.contains(e) ==> holds(a, e)),
{
    crate::ground::yield_is_grounded(sigma, bvars, universe);
    crate::spec::yield_sound(ctx, cl);
}

} // verus!
