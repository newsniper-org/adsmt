//! Invariant (iii): termination — a well-founded measure `d(C)` strictly decreases
//! on every CCFV search step, so the inner E-ground (dis)unification search cannot
//! diverge or yield infinitely. (Paper: the depth measure `d(C)`. Here: the number
//! of still-unsolved bound variables, which each ASSIGN strictly reduces.)
use vstd::prelude::*;
use crate::ground::EVar;

verus! {

/// The search measure `d(C)`: the number of bound variables not yet solved. The
/// search state is modelled as the sequence of still-pending bound variables.
pub open spec fn d_measure(pending: Seq<EVar>) -> nat {
    pending.len()
}

/// One search step (ASSIGN / U_VAR): solve one variable, dropping it from the
/// pending list. Precondition: there is at least one variable to solve.
pub open spec fn step(pending: Seq<EVar>) -> Seq<EVar>
    recommends
        pending.len() > 0,
{
    pending.drop_first()
}

/// Each step strictly decreases the measure — the core of the termination argument.
pub proof fn step_decreases(pending: Seq<EVar>)
    requires
        pending.len() > 0,
    ensures
        d_measure(step(pending)) < d_measure(pending),
{
    assert(step(pending).len() == pending.len() - 1);
}

/// The driving search recursion. The `decreases pending.len()` clause is the
/// well-foundedness obligation Verus discharges: because `step` reduces the
/// length, the recursion bottoms out — the CCFV inner search terminates and
/// cannot yield infinitely. `solve_depth` returns the number of steps taken.
pub open spec fn solve_depth(pending: Seq<EVar>) -> nat
    decreases pending.len(),
{
    if pending.len() == 0 {
        0
    } else {
        // recursive call on a strictly shorter pending list (well-founded)
        solve_depth(step(pending)) + 1
    }
}

/// The depth is exactly the initial number of pending variables — a closed form
/// confirming the search visits each variable once and then halts.
pub proof fn solve_depth_is_len(pending: Seq<EVar>)
    ensures
        solve_depth(pending) == pending.len(),
    decreases pending.len(),
{
    if pending.len() == 0 {
    } else {
        assert(step(pending).len() == pending.len() - 1);
        solve_depth_is_len(step(pending));
    }
}

} // verus!
