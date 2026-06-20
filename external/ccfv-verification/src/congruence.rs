//! STRENGTHENING — function congruence in the entailment model.
//!
//! This removes the original scaffold's biggest honest-scope caveat ("equality
//! fragment only; congruence assumed already closed by EUF"). Here the model
//! itself respects congruence (`respects_cong`), the congruence inference rule is
//! proved sound (`entails_cong`), and — the capstone — the WHOLE congruence-closure
//! discharge a CCFV YIELD performs is proved sound by **structural induction over a
//! derivation** (`CongProof` / `cong_proof_sound`). So YIELD-soundness now holds for
//! the full equality-with-congruence fragment CCFV actually matches over, not the
//! pure-equality skeleton — the soundness of matching *modulo congruence*.
use vstd::prelude::*;
use crate::spec::{EqLit, GTerm, Interp, holds, models};

verus! {

/// A function symbol.
pub type FSym = nat;

/// `app(f, x)` is the ground term `f(x)` — an abstract term constructor (unary is
/// enough to state the congruence axiom and chains to n-ary by repetition).
pub uninterp spec fn app(f: FSym, x: GTerm) -> GTerm;

/// A *congruence* interpretation: equal arguments map to equal applications. This
/// is the semantic content of "the model is a congruence" — the property the EUF
/// solver maintains and that makes E-matching-modulo-congruence sound.
pub open spec fn respects_cong(a: Interp) -> bool {
    forall|f: FSym, x: GTerm, y: GTerm| #![auto]
        a(x) == a(y) ==> a(app(f, x)) == a(app(f, y))
}

/// Entailment over **congruence** interpretations: every congruence model of `ctx`
/// satisfies `e`. (Quantifies over fewer interpretations than `spec::entails`, so
/// every `spec::entails` fact lifts here — and the congruence rule below holds.)
pub open spec fn entails_cc(ctx: Set<EqLit>, e: EqLit) -> bool {
    forall|a: Interp| respects_cong(a) && models(a, ctx) ==> holds(a, e)
}

// ----- the sound proof rules over `entails_cc` (refl/member/sym/trans + CONG) -----

pub proof fn entails_cc_refl(ctx: Set<EqLit>, t: GTerm)
    ensures
        entails_cc(ctx, EqLit { s: t, t: t }),
{
}

pub proof fn entails_cc_member(ctx: Set<EqLit>, e: EqLit)
    requires
        ctx.contains(e),
    ensures
        entails_cc(ctx, e),
{
    assert forall|a: Interp| #![auto] respects_cong(a) && models(a, ctx) implies holds(a, e) by {
        assert(ctx.contains(e));
    }
}

pub proof fn entails_cc_sym(ctx: Set<EqLit>, x: GTerm, y: GTerm)
    requires
        entails_cc(ctx, EqLit { s: x, t: y }),
    ensures
        entails_cc(ctx, EqLit { s: y, t: x }),
{
    assert forall|a: Interp| #![auto] respects_cong(a) && models(a, ctx) implies holds(a, EqLit {
        s: y,
        t: x,
    }) by {
        assert(holds(a, EqLit { s: x, t: y }));
    }
}

pub proof fn entails_cc_trans(ctx: Set<EqLit>, x: GTerm, y: GTerm, z: GTerm)
    requires
        entails_cc(ctx, EqLit { s: x, t: y }),
        entails_cc(ctx, EqLit { s: y, t: z }),
    ensures
        entails_cc(ctx, EqLit { s: x, t: z }),
{
    assert forall|a: Interp| #![auto] respects_cong(a) && models(a, ctx) implies holds(a, EqLit {
        s: x,
        t: z,
    }) by {
        assert(holds(a, EqLit { s: x, t: y }));
        assert(holds(a, EqLit { s: y, t: z }));
    }
}

/// THE CONGRUENCE RULE — the inference syntactic matching cannot make: from
/// `x ≃ y` conclude `f(x) ≃ f(y)`. Sound exactly because the model `respects_cong`.
pub proof fn entails_cong(ctx: Set<EqLit>, f: FSym, x: GTerm, y: GTerm)
    requires
        entails_cc(ctx, EqLit { s: x, t: y }),
    ensures
        entails_cc(ctx, EqLit { s: app(f, x), t: app(f, y) }),
{
    assert forall|a: Interp| #![auto] respects_cong(a) && models(a, ctx) implies holds(a, EqLit {
        s: app(f, x),
        t: app(f, y),
    }) by {
        assert(holds(a, EqLit { s: x, t: y }));      // a(x) == a(y)
        assert(a(app(f, x)) == a(app(f, y)));        // respects_cong @ (f, x, y)
    }
}

// ----- the YIELD discharge as a whole: a derivation, proved sound by induction -----

/// A congruence-closure derivation — a proof term for `ctx ⊢ s ≃ t` built from the
/// five sound rules. This is what the EUF/CCFV YIELD check implicitly constructs
/// when it decides a literal is discharged by the congruence.
pub enum CongProof {
    Refl(GTerm),
    Mem(EqLit),
    Sym(Box<CongProof>),
    Trans(Box<CongProof>, Box<CongProof>),
    Cong(FSym, Box<CongProof>),
}

/// The equality a derivation concludes.
pub open spec fn concludes(p: CongProof) -> EqLit
    decreases p,
{
    match p {
        CongProof::Refl(t) => EqLit { s: t, t: t },
        CongProof::Mem(e) => e,
        CongProof::Sym(q) => EqLit { s: concludes(*q).t, t: concludes(*q).s },
        CongProof::Trans(q, r) => EqLit { s: concludes(*q).s, t: concludes(*r).t },
        CongProof::Cong(f, q) => EqLit { s: app(f, concludes(*q).s), t: app(f, concludes(*q).t) },
    }
}

/// A derivation is *valid* against `ctx` when every leaf is `ctx`-justified and the
/// `Trans` middle terms line up.
pub open spec fn valid(ctx: Set<EqLit>, p: CongProof) -> bool
    decreases p,
{
    match p {
        CongProof::Refl(_) => true,
        CongProof::Mem(e) => ctx.contains(e),
        CongProof::Sym(q) => valid(ctx, *q),
        CongProof::Trans(q, r) => valid(ctx, *q) && valid(ctx, *r) && concludes(*q).t
            == concludes(*r).s,
        CongProof::Cong(_, q) => valid(ctx, *q),
    }
}

/// THE DERIVATION-SOUNDNESS THEOREM. Every valid congruence derivation concludes a
/// genuinely entailed equality — proved by structural induction over the proof
/// term, discharging each rule with its lemma above. This is the full soundness of
/// the YIELD congruence discharge (membership + reflexivity + symmetry +
/// transitivity + **function congruence**), not just rule-by-rule.
pub proof fn cong_proof_sound(ctx: Set<EqLit>, p: CongProof)
    requires
        valid(ctx, p),
    ensures
        entails_cc(ctx, concludes(p)),
    decreases p,
{
    match p {
        CongProof::Refl(t) => {
            entails_cc_refl(ctx, t);
        },
        CongProof::Mem(e) => {
            entails_cc_member(ctx, e);
        },
        CongProof::Sym(q) => {
            cong_proof_sound(ctx, *q);
            entails_cc_sym(ctx, concludes(*q).s, concludes(*q).t);
        },
        CongProof::Trans(q, r) => {
            cong_proof_sound(ctx, *q);
            cong_proof_sound(ctx, *r);
            assert(concludes(*q).t == concludes(*r).s);  // from valid
            entails_cc_trans(ctx, concludes(*q).s, concludes(*q).t, concludes(*r).t);
        },
        CongProof::Cong(f, q) => {
            cong_proof_sound(ctx, *q);
            entails_cong(ctx, f, concludes(*q).s, concludes(*q).t);
        },
    }
}

/// `Cσ` at YIELD is congruence-discharged when every literal has a valid derivation.
pub open spec fn clause_cong_provable(ctx: Set<EqLit>, cl: Set<EqLit>) -> bool {
    forall|e: EqLit| #[trigger] cl.contains(e) ==> exists|p: CongProof|
        valid(ctx, p) && concludes(p) == e
}

/// THE CONGRUENCE YIELD-SOUNDNESS THEOREM (strengthened invariant (i)). If the
/// congruence discharges every literal of `Cσ`, then every congruence model of
/// `E ∪ E_σ` satisfies all of `Cσ` — so closing the branch is sound even though
/// the discharge used function congruence the syntactic matcher could not.
pub proof fn cong_yield_sound(ctx: Set<EqLit>, cl: Set<EqLit>)
    requires
        clause_cong_provable(ctx, cl),
    ensures
        forall|a: Interp|
            respects_cong(a) && models(a, ctx) ==> (forall|e: EqLit|
                #[trigger] cl.contains(e) ==> holds(a, e)),
{
    assert forall|a: Interp| #![auto] respects_cong(a) && models(a, ctx) implies (forall|e: EqLit|
        #[trigger] cl.contains(e) ==> holds(a, e)) by {
        assert forall|e: EqLit| cl.contains(e) implies holds(a, e) by {
            let p = choose|p: CongProof| valid(ctx, p) && concludes(p) == e;
            cong_proof_sound(ctx, p);
            assert(entails_cc(ctx, e));
        }
    }
}

} // verus!
