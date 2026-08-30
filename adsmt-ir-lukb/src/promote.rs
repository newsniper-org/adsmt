// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! Recognise a TAGGED UNION written as `sort` + injections + projections, and
//! promote it to a real [`Item::Data`].
//!
//! # Why this exists
//!
//! Verus's AIR prelude declares what is structurally a datatype as an opaque
//! sort plus uninterpreted functions plus axioms:
//!
//! ```text
//! sort Poly
//! fn I(x0: Int): Poly        fn `%I`(x0: Poly): Int
//! fn B(x0: Bool): Poly       fn `%B`(x0: Poly): Bool
//! axiom: forall x: Int. x = `%I`(I(x))     trigger I(x)
//! ```
//!
//! It is written that way because AIR has nowhere to put the structure. The
//! lu-kb successor surface DOES — that is what "AIR to lu-kb-successor is less
//! lossy" buys — but the producer still emits the flattened form, so injectivity,
//! disjointness and the projection laws arrive as QUANTIFIED AXIOMS that the
//! instantiation loop has to rediscover at every solve. Promoted, they are facts
//! the datatype decision procedure holds for free.
//!
//! # What this pass is for, precisely
//!
//! It is a MEASUREMENT INSTRUMENT before it is an optimisation, and the
//! distinction matters. The `2026-08-30-n0-axiom-family-ablation` experiment
//! removed whole axiom families and saw nothing change — but removing an axiom
//! both shrinks the instantiation AND can destroy the proof, so a row that
//! stayed `unknown` might have done so for either reason. Promotion is the
//! intervention that separates them: the logical content is PRESERVED (the
//! datatype's laws are exactly injectivity + disjointness + the projection
//! equations) while the instantiation work disappears. If rows still do not
//! move under promotion, axiom volume is genuinely not the bottleneck.
//!
//! # Soundness
//!
//! Promotion REPLACES the recognised declarations with a `data` item and DROPS
//! the axioms it recognises as the datatype's own laws. Dropping an axiom that
//! the datatype theory does not actually entail would weaken `H`, which cannot
//! fabricate an `unsat`, but would silently lose proofs. Adding a datatype whose
//! laws are STRONGER than the axioms the source stated — disjointness the source
//! never asserted, say — could fabricate one. So:
//!
//! * a sort is promoted only when EVERY constructor's projection round-trip
//!   axiom (`∀x. x = %C(C(x))`) is present, and
//! * only those round-trip axioms are dropped. Every other axiom mentioning the
//!   sort is KEPT verbatim.
//!
//! The second rule is what keeps this from being a false-proof machine: an
//! axiom that says something about `Poly` beyond the round-trips survives, so
//! nothing the source asserted is lost, and nothing it did NOT assert is added
//! except the datatype's own injectivity/disjointness — which is where the
//! recognition risk actually lives.
//!
//! # Measured outcome on the real prelude: it does NOT fire, and that is the
//! finding
//!
//! Run against the 209-row verus corpus the recogniser reports **zero** unions.
//! `Poly` alone has eight functions returning it — `I`, `B`, `R`, `F`, plus
//! `mut_ref_current%`, `mut_ref_future%`, `fun_from_recursive_field`,
//! `Poly%tuple%0.` — and **nothing in the syntax says which four are
//! constructors**. The refusal rules above then correctly decline: a sort
//! carrying an un-round-tripped producer cannot be handed disjointness,
//! because `I(x) != other(y)` is a law the source never asserted and may not
//! hold.
//!
//! So the tagged union is not recoverable from the flattened form by
//! inspection. The structure has to come from the PRODUCER — verus emitting
//! `data Poly = …` instead of the sort-plus-axioms encoding, which is exactly
//! the "VIR producer retarget" that `docs/design/LUKB_SUCCESSOR_SURFACE.md`
//! §6 lists as the remaining piece of Phase 2. This module is then the
//! consumer-side check that the emitted form is what it claims to be, and the
//! A/B instrument (`ADSMT_PROMOTE_TAGGED_UNIONS=1` in `lukb_solve`) for
//! measuring what the retarget buys.

use crate::ast::{Ctor, Item, Module, Term, Type};

/// A recognised tagged union: the sort, its `(constructor, projection, payload
/// type)` triples, and the indices of the axioms that are exactly its
/// round-trip laws.
#[derive(Debug, Clone)]
pub struct TaggedUnion {
    /// The sort name (`Poly`).
    pub sort: String,
    /// `(injection, projection, payload type)` per constructor, in declaration
    /// order.
    pub ctors: Vec<(String, String, Type)>,
    /// Indices into the module's item list of the round-trip axioms this
    /// promotion subsumes. Every other item is preserved.
    pub subsumed_axioms: Vec<usize>,
}

/// Every tagged union in `m`, in declaration order. Read-only: use
/// [`promote_tagged_unions`] to rewrite.
#[must_use]
pub fn find_tagged_unions(m: &Module) -> Vec<TaggedUnion> {
    let mut out = Vec::new();
    for item in &m.items {
        let Item::Sort(s) = item else { continue };
        // Injections into `s`: a one-argument `fn` returning `s`.
        let mut injections: Vec<(String, Type)> = Vec::new();
        for it in &m.items {
            if let Item::Fn { name, params, ret, body: None } = it
                && *ret == Type::Name(s.clone())
                && let Some(t) = single_param(params)
                && t != Type::Name(s.clone())
            {
                injections.push((name.clone(), t));
            }
        }
        if injections.len() < 2 {
            // One constructor is not a union — and a zero-constructor sort is
            // just an opaque sort. Neither gains anything from promotion, and
            // both would gain a spurious "these are all the values" law.
            continue;
        }
        // A projection for each: a one-argument `fn` from `s` to the payload.
        let mut ctors = Vec::new();
        for (inj, payload) in &injections {
            let Some(proj) = m.items.iter().find_map(|it| match it {
                Item::Fn { name, params, ret, body: None }
                    if ret == payload
                        && single_param(params) == Some(Type::Name(s.clone())) =>
                {
                    Some(name.clone())
                }
                _ => None,
            }) else {
                ctors.clear();
                break;
            };
            ctors.push((inj.clone(), proj, payload.clone()));
        }
        if ctors.len() != injections.len() {
            continue;
        }
        let subsumed = round_trip_axiom_indices(m, &ctors);
        if subsumed.len() != ctors.len() {
            // Not every constructor's round-trip law is stated. Promoting would
            // hand the sort laws the source never asserted; refuse.
            continue;
        }
        out.push(TaggedUnion { sort: s.clone(), ctors, subsumed_axioms: subsumed });
    }
    out
}

/// Rewrite every recognised tagged union into an [`Item::Data`], dropping the
/// injections, projections and round-trip axioms it subsumes. Returns the new
/// module and the unions promoted.
#[must_use]
pub fn promote_tagged_unions(m: &Module) -> (Module, Vec<TaggedUnion>) {
    let unions = find_tagged_unions(m);
    if unions.is_empty() {
        return (m.clone(), unions);
    }
    let drop_axioms: Vec<usize> =
        unions.iter().flat_map(|u| u.subsumed_axioms.iter().copied()).collect();
    let mut items = Vec::with_capacity(m.items.len());
    for (i, it) in m.items.iter().enumerate() {
        if drop_axioms.contains(&i) {
            continue;
        }
        match it {
            Item::Sort(s) if unions.iter().any(|u| u.sort == *s) => {
                let u = unions.iter().find(|u| u.sort == *s).expect("just matched");
                let ctors: Vec<Ctor> = u
                    .ctors
                    .iter()
                    .map(|(inj, proj, ty)| {
                        (inj.clone(), vec![(Some(proj.clone()), ty.clone())])
                    })
                    .collect();
                items.push(Item::Data { name: s.clone(), ctors });
            }
            Item::Fn { name, .. }
                if unions.iter().any(|u| {
                    u.ctors.iter().any(|(inj, proj, _)| inj == name || proj == name)
                }) =>
            {
                // The `data` item declares both the constructor and its
                // selector; keeping the opaque `fn` too would shadow them.
            }
            other => items.push(other.clone()),
        }
    }
    (Module { items }, unions)
}

fn single_param(params: &[(Vec<String>, Type)]) -> Option<Type> {
    match params {
        [(names, t)] if names.len() == 1 => Some(t.clone()),
        _ => None,
    }
}

/// Indices of the axioms that are EXACTLY a constructor's round-trip law
/// `∀x. x = proj(inj(x))` (either orientation). Recognised structurally rather
/// than by name so a renamed prelude still matches.
fn round_trip_axiom_indices(m: &Module, ctors: &[(String, String, Type)]) -> Vec<usize> {
    let mut out = Vec::new();
    for (inj, proj, _) in ctors {
        for (i, it) in m.items.iter().enumerate() {
            if out.contains(&i) {
                continue;
            }
            let Item::Axiom(_, body) = it else { continue };
            if is_round_trip(body, inj, proj) {
                out.push(i);
                break;
            }
        }
    }
    out
}

/// `forall x: T. x = proj(inj(x))`, in either orientation, with any trigger.
fn is_round_trip(t: &Term, inj: &str, proj: &str) -> bool {
    let Term::Forall(binders, body, _) = t else { return false };
    let [b] = binders.as_slice() else { return false };
    let [v] = b.names.as_slice() else { return false };
    if b.constraint.is_some() {
        return false;
    }
    let Term::Bin(crate::ast::BinOp::Eq, a, c) = &**body else { return false };
    let one = |lhs: &Term, rhs: &Term| {
        matches!(lhs, Term::Var(n) if n == v) && is_proj_of_inj(rhs, inj, proj, v)
    };
    one(a, c) || one(c, a)
}

/// `proj(inj(v))`.
fn is_proj_of_inj(t: &Term, inj: &str, proj: &str, v: &str) -> bool {
    let Term::Call(f, args) = t else { return false };
    if f != proj || args.len() != 1 {
        return false;
    }
    let Term::Call(g, inner) = &args[0] else { return false };
    g == inj && inner.len() == 1 && matches!(&inner[0], Term::Var(n) if n == v)
}
