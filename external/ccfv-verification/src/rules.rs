//! STRENGTHENING — the CCFV search rule set refined onto a faithful state machine.
//!
//! Replaces `terminate`'s abstract "one bound variable per step" with the actual
//! CCFV rules over a real state `(E_σ, pending)` and the paper's variable-DEPTH
//! measure `d(C)`. Proves, **rule by rule**:
//!   - **grounding preservation** — every rule keeps `partial_grounded` (so the
//!     firewall property (ii) is an invariant of the whole search, not just the
//!     final YIELD), and
//!   - **measure decrease** — `ASSIGN` and `DECOMPOSE` (the U_* matching rule)
//!     each strictly decrease `d_measure`, so the search terminates with a real
//!     measure on real rules.
//!
//! Modelled rules: **ASSIGN** (bind a free var to a ground term in `T(E)` — the
//! firewall guard) and **DECOMPOSE** (`f(p) ≃ f(x)` ⟶ `p ≃ x`, the congruence
//! matching step). `SPLIT`/`FAIL` (disjunction branching / dead branch) are
//! terminal-or-non-increasing and left as the remaining abstraction (see lib docs).
use vstd::prelude::*;
use crate::spec::GTerm;
use crate::ground::{EVar, Subst, partial_grounded};
use crate::congruence::{FSym, app};

verus! {

/// A pattern term — the LHS of a matching constraint; may contain free variables.
pub enum PTerm {
    Var(EVar),
    Fun(FSym, Box<PTerm>),
}

/// The variable-depth of a pattern (the paper's `d` ingredient).
pub open spec fn depth(t: PTerm) -> nat
    decreases t,
{
    match t {
        PTerm::Var(_) => 0,
        PTerm::Fun(_, a) => 1 + depth(*a),
    }
}

/// An atomic matching constraint `pat ≃ rhs` (pattern against a ground term).
pub struct Atom {
    pub pat: PTerm,
    pub rhs: GTerm,
}

/// An atom's weight: `1 + depth` — the `1` makes ASSIGN (which removes a
/// depth-0 `Var` atom) strictly decrease the measure too.
pub open spec fn atom_weight(a: Atom) -> nat {
    1 + depth(a.pat)
}

/// `d_measure` — the search measure `d(C)`: the total weight of the pending atoms.
pub open spec fn d_measure(s: Seq<Atom>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        atom_weight(s[0]) + d_measure(s.drop_first())
    }
}

/// Appending an atom adds exactly its weight (the homomorphism the DECOMPOSE
/// measure-decrease proof needs). Proved by induction over the sequence.
pub proof fn d_measure_push(s: Seq<Atom>, a: Atom)
    ensures
        d_measure(s.push(a)) == d_measure(s) + atom_weight(a),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(a)[0] == a);
        assert(s.push(a).drop_first() =~= Seq::<Atom>::empty());
        assert(d_measure(s.push(a)) == atom_weight(a) + d_measure(Seq::<Atom>::empty()));
    } else {
        assert(s.push(a)[0] == s[0]);
        assert(s.push(a).drop_first() =~= s.drop_first().push(a));
        d_measure_push(s.drop_first(), a);
        assert(d_measure(s.push(a)) == atom_weight(s[0]) + d_measure(s.drop_first().push(a)));
    }
}

/// A CCFV search state: the partial solution `E_σ` and the pending constraint.
pub struct State {
    pub sigma: Subst,
    pub pending: Seq<Atom>,
}

/// The grounding invariant lifted to a state — `E_σ` binds only into `T(E)`.
pub open spec fn state_grounded(st: State, universe: Set<GTerm>) -> bool {
    partial_grounded(st.sigma, universe)
}

// ----- ASSIGN : a head `x ≃ g` binds the free var `x` to the ground term `g` -----

pub open spec fn assign_applicable(st: State) -> bool {
    st.pending.len() > 0 && (st.pending[0].pat is Var)
}

/// `pending` shrinks by the head (measure-independent of the variant); `sigma`
/// gains the binding `x ↦ g` (guarded to ground `g` by `assign_applicable` callers).
pub open spec fn assign_step(st: State) -> State {
    let head = st.pending[0];
    State {
        sigma: match head.pat {
            PTerm::Var(x) => st.sigma.insert(x, head.rhs),
            PTerm::Fun(_, _) => st.sigma,
        },
        pending: st.pending.drop_first(),
    }
}

/// ASSIGN preserves grounding when its bound term is in `T(E)` — the firewall guard.
pub proof fn assign_preserves_grounded(st: State, universe: Set<GTerm>)
    requires
        assign_applicable(st),
        state_grounded(st, universe),
        universe.contains(st.pending[0].rhs),
    ensures
        state_grounded(assign_step(st), universe),
{
    let head = st.pending[0];
    match head.pat {
        PTerm::Var(x) => {
            crate::ground::assign_preserves_grounding(st.sigma, x, head.rhs, universe);
        },
        PTerm::Fun(_, _) => {},
    }
}

/// ASSIGN strictly decreases the measure (it drops a weight-≥1 atom).
pub proof fn assign_decreases(st: State)
    requires
        assign_applicable(st),
    ensures
        d_measure(assign_step(st).pending) < d_measure(st.pending),
{
    assert(d_measure(st.pending) == atom_weight(st.pending[0]) + d_measure(
        st.pending.drop_first(),
    ));
}

// ----- DECOMPOSE (U_COMP) : `f(p) ≃ f(x)` ⟶ `p ≃ x` (the congruence match step) -----

/// Applicable when the head is `f(p) ≃ g` and `g` is the matching application
/// `app(f, x)` — exactly the `E^cc` signature-class hit the implementation finds.
pub open spec fn decompose_applicable(st: State, x: GTerm) -> bool {
    st.pending.len() > 0 && (match st.pending[0].pat {
        PTerm::Fun(f, _) => st.pending[0].rhs == app(f, x),
        PTerm::Var(_) => false,
    })
}

/// Replace the head `f(p) ≃ app(f,x)` with the strictly-shallower `p ≃ x`.
pub open spec fn decompose_step(st: State, x: GTerm) -> State {
    let head = st.pending[0];
    State {
        sigma: st.sigma,
        pending: match head.pat {
            PTerm::Fun(_, p) => st.pending.drop_first().push(Atom { pat: *p, rhs: x }),
            PTerm::Var(_) => st.pending.drop_first(),
        },
    }
}

/// DECOMPOSE preserves grounding trivially — it does not touch `E_σ`.
pub proof fn decompose_preserves_grounded(st: State, x: GTerm, universe: Set<GTerm>)
    requires
        state_grounded(st, universe),
    ensures
        state_grounded(decompose_step(st, x), universe),
{
}

/// DECOMPOSE strictly decreases the measure: it trades a depth-`d+1` atom (weight
/// `2 + depth(p)`) for a depth-`d` atom (weight `1 + depth(p)`).
pub proof fn decompose_decreases(st: State, x: GTerm)
    requires
        decompose_applicable(st, x),
    ensures
        d_measure(decompose_step(st, x).pending) < d_measure(st.pending),
{
    let head = st.pending[0];
    let rest = st.pending.drop_first();
    assert(d_measure(st.pending) == atom_weight(head) + d_measure(rest));
    match head.pat {
        PTerm::Fun(_, p) => {
            let new_atom = Atom { pat: *p, rhs: x };
            d_measure_push(rest, new_atom);
            assert(atom_weight(head) == 2 + depth(*p));
            assert(atom_weight(new_atom) == 1 + depth(*p));
        },
        PTerm::Var(_) => {},
    }
}

// ----- YIELD readiness: the terminal state of a converged search -----

/// A state is YIELD-ready when no constraint is pending — equivalently, the
/// measure has bottomed out at 0. Together with `assign_decreases` /
/// `decompose_decreases` (every non-terminal rule strictly lowers `d_measure`, a
/// well-founded `nat`) this is the termination argument with the *real* measure on
/// the *real* rules: the search reaches a YIELD-ready (or FAIL) state in finitely
/// many steps.
pub open spec fn yield_ready(st: State) -> bool {
    st.pending.len() == 0
}

pub proof fn yield_ready_iff_measure_zero(st: State)
    ensures
        yield_ready(st) <==> d_measure(st.pending) == 0,
{
    if st.pending.len() == 0 {
    } else {
        assert(d_measure(st.pending) == atom_weight(st.pending[0]) + d_measure(
            st.pending.drop_first(),
        ));
        assert(atom_weight(st.pending[0]) >= 1);
    }
}

} // verus!
