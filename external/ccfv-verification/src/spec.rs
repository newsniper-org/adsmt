//! Entailment semantics (non-vacuous) + invariant (i) YIELD-soundness.
//!
//! Fixes what `E ⊨ s ≃ t` MEANS so the YIELD-soundness theorem has real content.
//! An *interpretation* colors each ground term with an `int`; two terms are equal
//! in the model iff they get the same color — i.e. a coloring IS an equivalence
//! relation, the model-theoretic stand-in for a congruence. (Function congruence
//! is assumed already closed into the context by EUF — see the crate docs.)
use vstd::prelude::*;

verus! {

/// A ground term, identified by a `nat`.
pub type GTerm = nat;

/// An equality literal `s ≃ t`.
pub struct EqLit {
    pub s: GTerm,
    pub t: GTerm,
}

/// An interpretation / model: a coloring of ground terms. `a(x) == a(y)` means
/// "x and y are equal in this model". `==` on `int` is reflexive/symmetric/
/// transitive, so a coloring is automatically an equivalence relation.
pub type Interp = spec_fn(GTerm) -> int;

/// The literal `e` holds in model `a`.
pub open spec fn holds(a: Interp, e: EqLit) -> bool {
    a(e.s) == a(e.t)
}

/// `a` models the context `ctx` (a set of ground equalities, assumed
/// congruence-closed by EUF) when every equality in it holds.
pub open spec fn models(a: Interp, ctx: Set<EqLit>) -> bool {
    forall|e: EqLit| #[trigger] ctx.contains(e) ==> holds(a, e)
}

/// Semantic entailment: every model of `ctx` satisfies `e`. This is the precise
/// meaning of "the congruence `E ∪ E_σ` discharges literal `e`", which is exactly
/// what a CCFV YIELD checks before closing a branch.
pub open spec fn entails(ctx: Set<EqLit>, e: EqLit) -> bool {
    forall|a: Interp| models(a, ctx) ==> holds(a, e)
}

// ----- the sound proof rules CCFV's congruence/YIELD check composes -----
// Each is one inference the EUF closure + the (dis)unification rules use; proving
// them sound here is proving the YIELD discharge sound, rule by rule.

/// Reflexivity: `ctx ⊨ t ≃ t`.
pub proof fn entails_refl(ctx: Set<EqLit>, t: GTerm)
    ensures
        entails(ctx, EqLit { s: t, t: t }),
{
}

/// Membership (the U_VAR/ASSIGN base case): an equality in the context is entailed.
pub proof fn entails_member(ctx: Set<EqLit>, e: EqLit)
    requires
        ctx.contains(e),
    ensures
        entails(ctx, e),
{
    assert forall|a: Interp| #![auto] models(a, ctx) implies holds(a, e) by {
        assert(ctx.contains(e));
    }
}

/// Symmetry.
pub proof fn entails_sym(ctx: Set<EqLit>, x: GTerm, y: GTerm)
    requires
        entails(ctx, EqLit { s: x, t: y }),
    ensures
        entails(ctx, EqLit { s: y, t: x }),
{
    assert forall|a: Interp| #![auto] models(a, ctx) implies holds(a, EqLit { s: y, t: x }) by {
        assert(holds(a, EqLit { s: x, t: y }));
    }
}

/// Transitivity (chaining matched sub-terms through a shared class).
pub proof fn entails_trans(ctx: Set<EqLit>, x: GTerm, y: GTerm, z: GTerm)
    requires
        entails(ctx, EqLit { s: x, t: y }),
        entails(ctx, EqLit { s: y, t: z }),
    ensures
        entails(ctx, EqLit { s: x, t: z }),
{
    assert forall|a: Interp| #![auto] models(a, ctx) implies holds(a, EqLit { s: x, t: z }) by {
        assert(holds(a, EqLit { s: x, t: y }));
        assert(holds(a, EqLit { s: y, t: z }));
    }
}

/// Monotonicity: growing the context (CCFV's `E_σ` accumulating bindings) never
/// loses an entailment. This is why ASSIGN extending `E_σ` preserves soundness.
pub proof fn entails_mono(c1: Set<EqLit>, c2: Set<EqLit>, e: EqLit)
    requires
        c1.subset_of(c2),
        entails(c1, e),
    ensures
        entails(c2, e),
{
    assert forall|a: Interp| #![auto] models(a, c2) implies holds(a, e) by {
        assert forall|f: EqLit| #![auto] c1.contains(f) implies holds(a, f) by {
            assert(c2.contains(f));
        }
        assert(models(a, c1));
    }
}

// ----- invariant (i): YIELD-soundness -----

/// `Cσ` at a YIELD is a set of equality literals; the YIELD guard the algorithm
/// checks is "the context `ctx = E ∪ E_σ` entails every literal of `Cσ`".
pub open spec fn clause_entailed(ctx: Set<EqLit>, cl: Set<EqLit>) -> bool {
    forall|e: EqLit| #[trigger] cl.contains(e) ==> entails(ctx, e)
}

/// THE YIELD-SOUNDNESS THEOREM. If the YIELD guard holds (every literal of `Cσ`
/// is entailed by `E ∪ E_σ`), then every model of `E ∪ E_σ` satisfies all of
/// `Cσ`. So closing a branch never emits a binding the model refutes — the
/// never-conclude-unsat firewall stays sound under CCFV as the candidate source.
pub proof fn yield_sound(ctx: Set<EqLit>, cl: Set<EqLit>)
    requires
        clause_entailed(ctx, cl),
    ensures
        forall|a: Interp|
            models(a, ctx) ==> (forall|e: EqLit| #[trigger] cl.contains(e) ==> holds(a, e)),
{
    assert forall|a: Interp| models(a, ctx) implies (forall|e: EqLit|
        #[trigger] cl.contains(e) ==> holds(a, e)) by {
        assert forall|e: EqLit| cl.contains(e) implies holds(a, e) by {
            assert(entails(ctx, e));
        }
    }
}

} // verus!
