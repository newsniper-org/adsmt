//! Invariant (ii): grounding — every yielded `σ` maps the clause's bound variables
//! into the term universe `T(E)`. This is the property that makes the engine's
//! `instantiate` gate ("every replacement is a registered ground term",
//! `oxiz-mbqi/src/instantiate.rs`) satisfiable BY CONSTRUCTION, so CCFV never
//! fabricates a witness — the structural guard against spurious `unsat`.
use vstd::prelude::*;
use crate::spec::GTerm;

verus! {

/// A bound (universally-quantified) variable of the clause being instantiated.
pub type EVar = nat;

/// The partial solution `E_σ`: a map from bound variable to the ground term it has
/// been assigned. Grows by ASSIGN as the search descends.
pub type Subst = Map<EVar, GTerm>;

/// PARTIAL grounding: every variable ALREADY bound by `sigma` maps into the term
/// universe `T(E) = universe`. The search invariant maintained at every state.
pub open spec fn partial_grounded(sigma: Subst, universe: Set<GTerm>) -> bool {
    forall|v: EVar| #[trigger] sigma.dom().contains(v) ==> universe.contains(sigma[v])
}

/// FULL grounding at YIELD: every bound variable `bvars` of the clause is assigned,
/// and to a term in `T(E)`. This is what the `instantiate` gate requires.
pub open spec fn grounded(sigma: Subst, bvars: Set<EVar>, universe: Set<GTerm>) -> bool {
    forall|v: EVar|
        #[trigger] bvars.contains(v) ==> sigma.dom().contains(v) && universe.contains(sigma[v])
}

/// ASSIGN: bind variable `x` to ground term `t`. The firewall guard is the
/// precondition `t ∈ universe` — CCFV only ever grounds to a term in `E`.
pub open spec fn assign(sigma: Subst, x: EVar, t: GTerm) -> Subst {
    sigma.insert(x, t)
}

/// ASSIGN preserves the partial-grounding invariant when the new term is in the
/// universe. (Establishing the invariant is maintained step by step.)
pub proof fn assign_preserves_grounding(sigma: Subst, x: EVar, t: GTerm, universe: Set<GTerm>)
    requires
        partial_grounded(sigma, universe),
        universe.contains(t),
    ensures
        partial_grounded(assign(sigma, x, t), universe),
{
    let s2 = assign(sigma, x, t);
    assert forall|v: EVar| #![auto] s2.dom().contains(v) implies universe.contains(s2[v]) by {
        if v == x {
            assert(s2[x] == t);
        } else {
            // dom(insert(x,t)) = dom(sigma) ∪ {x}; v != x ⇒ v ∈ dom(sigma) and s2[v] == sigma[v]
            assert(sigma.dom().contains(v));
            assert(s2[v] == sigma[v]);
        }
    }
}

/// THE GROUNDING THEOREM. At a YIELD, if the partial-grounding invariant holds and
/// every bound variable of the clause is assigned, then `σ` is fully grounded into
/// `T(E)` — so the emitted instance passes the `instantiate` gate by construction.
pub proof fn yield_is_grounded(sigma: Subst, bvars: Set<EVar>, universe: Set<GTerm>)
    requires
        partial_grounded(sigma, universe),
        forall|v: EVar| #[trigger] bvars.contains(v) ==> sigma.dom().contains(v),
    ensures
        grounded(sigma, bvars, universe),
{
    assert forall|v: EVar| #![auto] bvars.contains(v) implies (sigma.dom().contains(v)
        && universe.contains(sigma[v])) by {
        assert(sigma.dom().contains(v));
    }
}

} // verus!
