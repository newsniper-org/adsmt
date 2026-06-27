//! The `*Like` number-system type-relation family — first slice.
//!
//! This module declares the two integer-side relations of the family the
//! user calls *type relations* (each instance — single- or multi-parameter —
//! is a relation between types/theories):
//!
//! * [`partial_integer_like`] — `PartialIntegerLike(I)`, the **superclass**:
//!   an integer-like commutative core (closed under `+`, `*`) carrying a
//!   per-carrier **validity / positivity predicate** `domain : I -> Bool`.
//!   No `zero` (0 ∉ `Nat` in the lukb lattice), no `neg`/`sub` (`Nat`/`WNat`
//!   are not closed under subtraction — guard G6), and no order (a future
//!   `ComplexIntegerLike` sibling, ℤ[i]/ℤ[ω], has no total order).
//! * [`integer_like`] — `IntegerLike(I)`, the **subtrait**: adds the order
//!   operation `le : I -> I -> Bool` and (the deferred gating goal-member)
//!   the **total-order law**. Every `IntegerLike` instance carries the
//!   premise `PartialIntegerLike(I)`. This mirrors Rust's `Eq: PartialEq` /
//!   `Ord: PartialOrd`: the subtrait adds a law a carrier must satisfy to be
//!   admitted (ℤ[i] resolves to `PartialIntegerLike` but **not** `IntegerLike`,
//!   exactly as float fails `Eq`).
//!
//! The three ground instances are the lukb arithmetic carriers
//! `Int`/`Nat`/`WNat`. Their dictionaries' single soundly-expressible payload
//! at this slice is the `domain` predicate — the **positivity** the type
//! relation contributes that the engine does not already know:
//! `Int ↦ ⊤`, `WNat ↦ wnat2int x ≥ 0`, `Nat ↦ nat2int x ≥ 1`. This is the
//! lever the lukb-utilisation audit identified (`Nat ⟹ ≥1`, `WNat ⟹ ≥0`):
//! routing a refinement-sort variable into LIA with its defining constraint.
//!
//! The arithmetic ops `add`/`mul` and the order `le` are declared as the
//! dictionary *contract* (method signatures) but their refinement-sort
//! bodies require the `Reduces` encode/decode reduction spine (carrier →
//! Int image → LIA and back); those bodies land with the next slice. Only the
//! `Int` carrier — a genuine ring — wires them directly to the engine ops
//! here. Instance method-completeness is intentionally *not* enforced by
//! [`InstanceDb`]; the dictionary is populated in stages.
//!
//! Resolution is the same SLD walk type inference uses, so a single declared
//! instance serves all four interlocking engines (type inference, abduction,
//! ASP, SMT) — see the `four-way-interlock-design-intent` /
//! `numberlike-family-design` design notes.

use std::sync::Arc;

use adsmt_core::{Kind, Term, TyVar, Type, Var};

use crate::instance::{Instance, Premise};
use crate::relation::Relation;
use crate::resolve::InstanceDb;

// ── relation names ──────────────────────────────────────────────────────
pub const PARTIAL_INTEGER_LIKE: &str = "PartialIntegerLike";
pub const INTEGER_LIKE: &str = "IntegerLike";

// ── method names ────────────────────────────────────────────────────────
/// In-carrier validity / positivity predicate `I -> Bool`.
pub const M_DOMAIN: &str = "domain";
/// Carrier addition `I -> I -> I`.
pub const M_ADD: &str = "add";
/// Carrier multiplication `I -> I -> I`.
pub const M_MUL: &str = "mul";
/// Total order `I -> I -> Bool` (lives on `IntegerLike`).
pub const M_LE: &str = "le";

// ── carrier sort + engine op names ──────────────────────────────────────
//
// These mirror `adsmt_ir::theory` (the CIC kernel's postulated sorts,
// injections, and Int operators) by *value*. They are duplicated here as
// plain string literals rather than imported because the type-class layer
// (`adsmt-class`) sits *below* `adsmt-ir` and must not depend on it; a
// shared dependency would invert the workspace layering. The lowering slice
// that consumes these dictionaries matches against the same names.
const SORT_INT: &str = "Int";
const SORT_NAT: &str = "Nat";
const SORT_WNAT: &str = "WNat";

const NAT2INT: &str = "nat2int";
const WNAT2INT: &str = "wnat2int";

const INT_ADD: &str = "Int.add";
const INT_MUL: &str = "Int.mul";
const INT_LE: &str = "Int.le";

fn int_ty() -> Type {
    Type::const_(SORT_INT, Kind::Type)
}

fn carrier_ty(sort: &str) -> Type {
    Type::const_(sort, Kind::Type)
}

/// `op : a -> b -> c`, a curried binary engine operator.
fn binop_const(name: &str, a: Type, b: Type, c: Type) -> Term {
    let ty = Type::fun(a, Type::fun(b, c).expect("kind")).expect("kind");
    Term::const_(name, ty)
}

/// `inj : from -> Int`, a kernel injection into the integers.
fn injection_const(name: &str, from: Type) -> Term {
    Term::const_(name, Type::fun(from, int_ty()).expect("kind"))
}

/// Build the `domain` dictionary body `λ(x : carrier). lo ≤ ι(x)`, i.e. the
/// positivity guard `Int.le lo (inj x)`. For `Int` the injection is the
/// identity and there is no lower bound, so the body is `λ(x : Int). ⊤`.
fn domain_body(sort: &str) -> Term {
    let carrier = carrier_ty(sort);
    let x = Var { name: "x".into(), ty: carrier.clone() };
    let xt = Term::Var(Arc::new(x.clone()));

    let body = match sort {
        SORT_INT => Term::true_const(),
        SORT_WNAT => positivity_guard(WNAT2INT, carrier.clone(), xt, 0),
        SORT_NAT => positivity_guard(NAT2INT, carrier.clone(), xt, 1),
        other => unreachable!("domain_body called on non-carrier sort {other}"),
    };
    Term::lam(x, body)
}

/// `Int.le <lo> (inj x)` — the carrier's lower-bound positivity constraint
/// over its integer image.
fn positivity_guard(inj: &str, carrier: Type, xt: Term, lo: i128) -> Term {
    let img = Term::app(injection_const(inj, carrier), xt).expect("injection well-typed");
    let lo_lit = Term::const_(&lo.to_string(), int_ty());
    let le = binop_const(INT_LE, int_ty(), int_ty(), Type::bool_());
    let partial = Term::app(le, lo_lit).expect("Int.le on a literal");
    Term::app(partial, img).expect("Int.le on the image")
}

/// The `PartialIntegerLike(I)` relation: the integer-like commutative core
/// plus a per-carrier validity predicate. `I : Type` is first-order (the HKT
/// of the wider family is realised as a value-level `Premise` edge, never a
/// kinded parameter).
pub fn partial_integer_like() -> Relation {
    let i = Arc::new(TyVar { name: "I".into(), kind: Kind::Type });
    let it = Type::Var(i.clone());
    Relation::new(PARTIAL_INTEGER_LIKE)
        .with_param(i)
        .with_method(M_ADD, fun3(it.clone(), it.clone(), it.clone()))
        .with_method(M_MUL, fun3(it.clone(), it.clone(), it.clone()))
        .with_method(M_DOMAIN, Type::fun(it, Type::bool_()).expect("kind"))
}

/// The `IntegerLike(I)` subtrait: adds the total order `le` (the total-order
/// law is the deferred gating goal-member). Instances premise
/// `PartialIntegerLike(I)`.
pub fn integer_like() -> Relation {
    let i = Arc::new(TyVar { name: "I".into(), kind: Kind::Type });
    let it = Type::Var(i.clone());
    Relation::new(INTEGER_LIKE)
        .with_param(i)
        .with_method(M_LE, fun3(it.clone(), it, Type::bool_()))
}

/// `a -> b -> c`.
fn fun3(a: Type, b: Type, c: Type) -> Type {
    Type::fun(a, Type::fun(b, c).expect("kind")).expect("kind")
}

/// `PartialIntegerLike(sort)` ground instance carrying the `domain`
/// positivity dictionary. For `Int` the ring ops `add`/`mul` are wired
/// directly to the engine operators; for the refinement carriers they await
/// the `Reduces` reduction spine.
fn partial_instance(sort: &str) -> Instance {
    let carrier = carrier_ty(sort);
    let mut inst = Instance::new(PARTIAL_INTEGER_LIKE, vec![carrier.clone()])
        .with_method(M_DOMAIN, domain_body(sort));
    if sort == SORT_INT {
        inst = inst
            .with_method(M_ADD, binop_const(INT_ADD, carrier.clone(), carrier.clone(), carrier.clone()))
            .with_method(M_MUL, binop_const(INT_MUL, carrier.clone(), carrier.clone(), carrier));
    }
    inst
}

/// `IntegerLike(sort)` ground instance: premises `PartialIntegerLike(sort)`
/// and (for `Int`) wires the order op to the engine `Int.le`.
fn integer_instance(sort: &str) -> Instance {
    let carrier = carrier_ty(sort);
    let mut inst = Instance::new(INTEGER_LIKE, vec![carrier.clone()])
        .with_premise(Premise::new(PARTIAL_INTEGER_LIKE, vec![carrier.clone()]));
    if sort == SORT_INT {
        inst = inst.with_method(M_LE, binop_const(INT_LE, carrier.clone(), carrier, Type::bool_()));
    }
    inst
}

/// Install the two integer-side relations and their `Int`/`Nat`/`WNat`
/// ground instances into `db`. Returns the same `db` for chaining.
///
/// Panics only on an internal coherence/arity bug (the heads are distinct
/// carrier constants, so no overlap is possible) — a failure here is a
/// programming error in this module, not user input.
pub fn install_numberlike(db: &mut InstanceDb) {
    db.declare_relation(partial_integer_like());
    db.declare_relation(integer_like());
    for sort in [SORT_INT, SORT_NAT, SORT_WNAT] {
        db.declare_instance(partial_instance(sort))
            .expect("PartialIntegerLike ground instance");
        db.declare_instance(integer_instance(sort))
            .expect("IntegerLike ground instance");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolve::{ClassGoal, ResolutionResult, Resolver};
    use adsmt_core::TermInner;

    fn db() -> InstanceDb {
        let mut db = InstanceDb::new();
        install_numberlike(&mut db);
        db
    }

    #[test]
    fn integer_like_resolves_with_partial_subgoal() {
        let db = db();
        let goal = ClassGoal::new(INTEGER_LIKE, vec![int_ty()]);
        match Resolver::new(&db).resolve(&goal) {
            ResolutionResult::Found(m) => {
                assert_eq!(m.sub_goals.len(), 1, "IntegerLike must premise PartialIntegerLike");
                assert_eq!(m.sub_goals[0].relation, PARTIAL_INTEGER_LIKE);
                assert_eq!(m.sub_goals[0].types[0], int_ty());
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn partial_integer_like_resolves_without_subgoals() {
        let db = db();
        for sort in [SORT_INT, SORT_NAT, SORT_WNAT] {
            let goal = ClassGoal::new(PARTIAL_INTEGER_LIKE, vec![carrier_ty(sort)]);
            match Resolver::new(&db).resolve(&goal) {
                ResolutionResult::Found(m) => assert!(m.sub_goals.is_empty()),
                other => panic!("expected Found for {sort}, got {other:?}"),
            }
        }
    }

    #[test]
    fn all_three_carriers_are_integer_like() {
        let db = db();
        for sort in [SORT_INT, SORT_NAT, SORT_WNAT] {
            let goal = ClassGoal::new(INTEGER_LIKE, vec![carrier_ty(sort)]);
            assert!(
                matches!(Resolver::new(&db).resolve(&goal), ResolutionResult::Found(_)),
                "{sort} should be IntegerLike",
            );
        }
    }

    #[test]
    fn unregistered_carrier_is_not_found() {
        let db = db();
        // `Bool` is not an integer-like carrier — no instance head matches.
        let goal = ClassGoal::new(INTEGER_LIKE, vec![Type::bool_()]);
        assert!(matches!(
            Resolver::new(&db).resolve(&goal),
            ResolutionResult::NotFound
        ));
    }

    #[test]
    fn nat_domain_is_the_positivity_predicate() {
        // The Nat dictionary's `domain` body must be λx. Int.le 1 (nat2int x):
        // a lambda whose body applies `Int.le` to the literal `1` and the
        // `nat2int` image of the bound variable. This is the #338 lever.
        let inst = partial_instance(SORT_NAT);
        let domain = inst
            .methods
            .iter()
            .find(|m| m.name == M_DOMAIN)
            .expect("Nat has a domain method");
        // Outer shape: a lambda over a Nat-sorted binder, Bool body.
        match domain.body.kind() {
            TermInner::Lam(v, body) => {
                assert_eq!(v.ty, carrier_ty(SORT_NAT));
                assert_eq!(body.type_of(), Type::bool_());
                // The body must mention nat2int and Int.le and the literal 1.
                let s = format!("{body:?}");
                assert!(s.contains(NAT2INT), "domain routes through nat2int: {s}");
                assert!(s.contains(INT_LE), "domain asserts an Int.le bound: {s}");
            }
            other => panic!("expected a lambda domain body, got {other:?}"),
        }
    }

    #[test]
    fn wnat_lower_bound_is_zero_nat_is_one() {
        // WNat admits 0 (≥0); Nat does not (≥1). The literals differ.
        let wnat = format!("{:?}", partial_instance(SORT_WNAT).methods[0].body);
        let nat = format!("{:?}", partial_instance(SORT_NAT).methods[0].body);
        assert!(wnat.contains(WNAT2INT) && wnat.contains("\"0\""), "WNat ≥ 0: {wnat}");
        assert!(nat.contains(NAT2INT) && nat.contains("\"1\""), "Nat ≥ 1: {nat}");
    }

    #[test]
    fn int_domain_is_trivially_true() {
        // Int admits every value — its validity predicate is ⊤, no injection.
        let inst = partial_instance(SORT_INT);
        let domain = &inst.methods.iter().find(|m| m.name == M_DOMAIN).unwrap().body;
        match domain.kind() {
            TermInner::Lam(_, body) => assert!(body.is_true_const(), "Int domain is ⊤"),
            other => panic!("expected λ, got {other:?}"),
        }
    }

    #[test]
    fn re_declaring_a_carrier_violates_coherence() {
        // Sanity: the DB enforces coherence on these heads.
        let mut db = db();
        let err = db.declare_instance(integer_instance(SORT_INT)).unwrap_err();
        assert_eq!(err, crate::resolve::ClassError::CoherenceViolation);
    }
}
