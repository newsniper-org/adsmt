//! The `*Like` number-system type-relation family + the order relations it
//! builds on.
//!
//! This module declares, as real `adsmt-class` relations (the user's *type
//! relations* — each instance is a relation between types/theories):
//!
//! **Order axis** (standalone, so the `*Like` relations reuse it rather than
//! each re-declaring an order):
//! * [`partial_ord`] — `PartialOrd(I)`: a partial order `le : I -> I -> Bool`
//!   with the goal-members (laws) *reflexivity*, *antisymmetry*, *transitivity*.
//! * [`ord`] — `Ord(I) : PartialOrd(I)`: the total-order subtrait. Adds the
//!   *totality* law (`∀a b. le a b ∨ le b a`) and **no new method** — `le` is
//!   inherited through the `PartialOrd` premise (the Rust `Ord: PartialOrd` /
//!   `Eq: PartialEq` shape).
//!
//! **Integer axis:**
//! * [`partial_integer_like`] — `PartialIntegerLike(I)`: the integer-like
//!   commutative core `{add, mul, domain}` (validity/positivity predicate). No
//!   `zero` (0 ∉ `Nat`), no `neg`/`sub` (`Nat`/`WNat` not subtraction-closed),
//!   no order.
//! * [`integer_like`] — `IntegerLike(I) : PartialIntegerLike(I), Ord(I)`: an
//!   integer-like carrier that is *also* totally ordered. A pure conjunction
//!   marker — its laws and methods are inherited through the two premises.
//!   ℤ, ℕ, WNat are `IntegerLike`; a future `ComplexIntegerLike` (ℤ[i]/ℤ[ω])
//!   will premise `PartialIntegerLike` but **not** `Ord`.
//!
//! **Field axis** (the scalar-field sibling of the integer axis):
//! * [`real_like`] — `RealLike(R)`: a field-like carrier `{add, mul, domain}`
//!   whose order is supplied through its instance's `PartialOrd(R)` premise. The
//!   genuine `Real` is additionally declared `Ord(Real)` (a separate instance,
//!   not a `RealLike` premise) — a `FloatingPoint` carrier would be `RealLike` +
//!   `PartialOrd` but **not** `Ord` (`NaN` breaks totality). `Real`'s `le` is the
//!   native `Real.le` (LRA) and its `domain` is the whole field (`λx. ⊤`).
//!   `ComplexIntegerLike` (ℤ[i]/ℤ[ω]) and `ComplexLike` (ℂ) — the `Pair`-rep
//!   minpoly extensions over an `IntegerLike`/`RealLike` base — are the next
//!   members (they need the `Reduces` encode/decode spine + the G1 irreducibility
//!   gate; NIA/NRA-abstaining until oxiz-nl2 is on the polite bus).
//!
//! The order laws are the canonical use of proof-gated admission ([`Law`],
//! [`crate::InstanceDb::declare_instance_lawful`]): an `Ord` instance is
//! admitted only if the solver discharges *totality* for its `le`; a carrier
//! with no compatible total order (e.g. a future `FloatingPoint(M, E)` with
//! `NaN`) is rejected by that gate and stays `PartialOrd` only.
//!
//! Ground instances are the lukb arithmetic carriers `Int`/`Nat`/`WNat`. Their
//! soundly-expressible dictionary content this slice:
//! * `le` — `Int ↦ Int.le`; `Nat/WNat ↦ λa b. Int.le (ι a) (ι b)` (the order is
//!   the restriction of ℤ's via the injection ι — a `Bool` result needs no
//!   back-injection, so this is total and sound).
//! * `domain` — `Int ↦ ⊤`, `WNat ↦ ι x ≥ 0`, `Nat ↦ ι x ≥ 1` (the #338
//!   positivity lever).
//!
//! `add`/`mul` (carrier-valued results) await the `Reduces` encode/decode spine
//! and are wired only for the `Int` ring here. Sort/op/injection names mirror
//! `adsmt_ir::theory` by value (this crate sits below `adsmt-ir`).

use std::sync::Arc;

use adsmt_core::{Kind, Term, TyVar, Type, Var};

use crate::instance::{Instance, Premise};
use crate::law::{Dict, Law, LawError, LawProver};
use crate::relation::Relation;
use crate::resolve::{ClassError, InstanceDb};

// ── relation names ──────────────────────────────────────────────────────
pub const PARTIAL_ORD: &str = "PartialOrd";
pub const ORD: &str = "Ord";
pub const PARTIAL_INTEGER_LIKE: &str = "PartialIntegerLike";
pub const INTEGER_LIKE: &str = "IntegerLike";
/// `RealLike(R)` — a totally-/densely-ordered field-like carrier (the field-side
/// sibling of `IntegerLike`). Premises `PartialOrd(R)` at the instance level
/// (every real-like carrier is at least partially ordered — a `FloatingPoint`
/// carrier would be `RealLike` + `PartialOrd` but **not** `Ord`, since `NaN`
/// breaks totality). The genuine mathematical `Real` is additionally declared
/// `Ord(Real)` (a separate instance, not a `RealLike` premise).
pub const REAL_LIKE: &str = "RealLike";

// ── method names ────────────────────────────────────────────────────────
/// Order `I -> I -> Bool` (lives on `PartialOrd`).
pub const M_LE: &str = "le";
/// In-carrier validity / positivity predicate `I -> Bool`.
pub const M_DOMAIN: &str = "domain";
/// Carrier addition `I -> I -> I`.
pub const M_ADD: &str = "add";
/// Carrier multiplication `I -> I -> I`.
pub const M_MUL: &str = "mul";

// ── carrier sort + engine op names ──────────────────────────────────────
//
// Mirrored by value from `adsmt_ir::theory`. `adsmt-class` sits below
// `adsmt-ir` and must not depend on it; the lowering slice that consumes these
// dictionaries matches against the same names.
const SORT_INT: &str = "Int";
const SORT_NAT: &str = "Nat";
const SORT_WNAT: &str = "WNat";
const SORT_REAL: &str = "Real";

const NAT2INT: &str = "nat2int";
const WNAT2INT: &str = "wnat2int";

const INT_ADD: &str = "Int.add";
const INT_MUL: &str = "Int.mul";
const INT_LE: &str = "Int.le";

const REAL_ADD: &str = "Real.add";
const REAL_MUL: &str = "Real.mul";
const REAL_LE: &str = "Real.le";

fn int_ty() -> Type {
    Type::const_(SORT_INT, Kind::Type)
}

fn carrier_ty(sort: &str) -> Type {
    Type::const_(sort, Kind::Type)
}

fn tyvar(name: &str) -> Arc<TyVar> {
    Arc::new(TyVar { name: name.into(), kind: Kind::Type })
}

/// `a -> b -> c`.
fn fun3(a: Type, b: Type, c: Type) -> Type {
    Type::fun(a, Type::fun(b, c).expect("kind")).expect("kind")
}

/// `op : a -> b -> c`, a curried binary engine operator.
fn binop_const(name: &str, a: Type, b: Type, c: Type) -> Term {
    Term::const_(name, fun3(a, b, c))
}

/// `inj : from -> Int`, a kernel injection into the integers.
fn injection_const(name: &str, from: Type) -> Term {
    Term::const_(name, Type::fun(from, int_ty()).expect("kind"))
}

// ── relations ───────────────────────────────────────────────────────────

/// `PartialOrd(I)`: a partial order with reflexivity / antisymmetry /
/// transitivity laws.
pub fn partial_ord() -> Relation {
    let i = tyvar("I");
    let it = Type::Var(i.clone());
    Relation::new(PARTIAL_ORD)
        .with_param(i)
        .with_method(M_LE, fun3(it.clone(), it, Type::bool_()))
        .with_law(Law::new("reflexivity", law_reflexivity))
        .with_law(Law::new("antisymmetry", law_antisymmetry))
        .with_law(Law::new("transitivity", law_transitivity))
}

/// `Ord(I) : PartialOrd(I)`: the total-order subtrait. Adds the totality law
/// and no new method (`le` is inherited through the `PartialOrd` premise).
pub fn ord() -> Relation {
    Relation::new(ORD)
        .with_param(tyvar("I"))
        .with_law(Law::new("totality", law_totality))
}

/// `PartialIntegerLike(I)`: the integer-like commutative core plus a per-carrier
/// validity predicate. No `zero`, no `neg`/`sub`, no order.
pub fn partial_integer_like() -> Relation {
    let i = tyvar("I");
    let it = Type::Var(i.clone());
    Relation::new(PARTIAL_INTEGER_LIKE)
        .with_param(i)
        .with_method(M_ADD, fun3(it.clone(), it.clone(), it.clone()))
        .with_method(M_MUL, fun3(it.clone(), it.clone(), it.clone()))
        .with_method(M_DOMAIN, Type::fun(it, Type::bool_()).expect("kind"))
}

/// `IntegerLike(I) : PartialIntegerLike(I), Ord(I)`: integer-like and totally
/// ordered. A conjunction marker — instances carry both premises and no own
/// methods or laws.
pub fn integer_like() -> Relation {
    Relation::new(INTEGER_LIKE).with_param(tyvar("I"))
}

/// `RealLike(R)`: the field-side scalar carrier (the totally-/densely-ordered
/// field analogue of `PartialIntegerLike`). Same commutative core `{add, mul,
/// domain}`; the order is supplied through the instance's `PartialOrd(R)` premise
/// (and, for the genuine `Real`, a separate `Ord(Real)` instance). No own laws —
/// the order laws live on `PartialOrd`/`Ord`.
pub fn real_like() -> Relation {
    let r = tyvar("R");
    let rt = Type::Var(r.clone());
    Relation::new(REAL_LIKE)
        .with_param(r)
        .with_method(M_ADD, fun3(rt.clone(), rt.clone(), rt.clone()))
        .with_method(M_MUL, fun3(rt.clone(), rt.clone(), rt.clone()))
        .with_method(M_DOMAIN, Type::fun(rt, Type::bool_()).expect("kind"))
}

// ── order laws (goal-members) ───────────────────────────────────────────
//
// Each builds a closed `Bool`-typed obligation over the instance's `le` (which
// the premise-aware `Dict` resolves, for an `Ord` instance, through its
// `PartialOrd` premise). Applications are β-reduced so an injection-defined `le`
// (`λa b. Int.le (ι a) (ι b)`) yields a clean atomic comparison.

fn law_reflexivity(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let le = d.require(M_LE)?;
    let a = Term::var("a", c.clone());
    let body = apply2(&le, a.clone(), a)?; // le a a
    close_forall(&c, &["a"], body)
}

fn law_antisymmetry(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let le = d.require(M_LE)?;
    let a = Term::var("a", c.clone());
    let b = Term::var("b", c.clone());
    let ab = apply2(&le, a.clone(), b.clone())?;
    let ba = apply2(&le, b.clone(), a.clone())?;
    // (le a b ∧ le b a) ⟹ a = b
    let imp = Term::mk_imp(Term::mk_and(ab, ba)?, Term::mk_eq(a, b)?)?;
    close_forall(&c, &["a", "b"], imp)
}

fn law_transitivity(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let le = d.require(M_LE)?;
    let a = Term::var("a", c.clone());
    let b = Term::var("b", c.clone());
    let cc = Term::var("c", c.clone());
    let ab = apply2(&le, a.clone(), b.clone())?;
    let bc = apply2(&le, b.clone(), cc.clone())?;
    let ac = apply2(&le, a, cc)?;
    // (le a b ∧ le b c) ⟹ le a c
    let imp = Term::mk_imp(Term::mk_and(ab, bc)?, ac)?;
    close_forall(&c, &["a", "b", "c"], imp)
}

fn law_totality(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let le = d.require(M_LE)?;
    let a = Term::var("a", c.clone());
    let b = Term::var("b", c.clone());
    let ab = apply2(&le, a.clone(), b.clone())?;
    let ba = apply2(&le, b, a)?;
    let disj = Term::mk_or(ab, ba)?; // le a b ∨ le b a
    close_forall(&c, &["a", "b"], disj)
}

/// `f x`, β-reducing the redex when `f` is a λ (so an injection-defined `le`
/// collapses), and leaving the application as-is when `f`'s head is a constant.
fn app_beta(f: Term, x: Term) -> Result<Term, LawError> {
    let applied = Term::app(f, x)?;
    Ok(applied.beta_reduce().unwrap_or(applied))
}

/// `f x y`, β-reduced.
fn apply2(f: &Term, x: Term, y: Term) -> Result<Term, LawError> {
    app_beta(app_beta(f.clone(), x)?, y)
}

/// Universally close `body` over `names`, each a binder of carrier sort.
fn close_forall(carrier: &Type, names: &[&str], body: Term) -> Result<Term, LawError> {
    let mut t = body;
    for name in names.iter().rev() {
        let v = Var { name: (*name).to_string(), ty: carrier.clone() };
        t = Term::mk_forall(v, t)?;
    }
    Ok(t)
}

// ── ground instances ────────────────────────────────────────────────────

/// The carrier's `le` body. `Int ↦ Int.le`; refinement carriers route through
/// their integer injection (sound: the result is `Bool`, no back-injection).
fn le_body(sort: &str) -> Term {
    let carrier = carrier_ty(sort);
    match sort {
        SORT_INT => binop_const(INT_LE, carrier.clone(), carrier, Type::bool_()),
        SORT_REAL => binop_const(REAL_LE, carrier.clone(), carrier, Type::bool_()),
        SORT_NAT => injected_le(NAT2INT, carrier),
        SORT_WNAT => injected_le(WNAT2INT, carrier),
        other => unreachable!("le_body on non-carrier {other}"),
    }
}

/// `λ(x : carrier)(y : carrier). Int.le (inj x) (inj y)`.
fn injected_le(inj: &str, carrier: Type) -> Term {
    let x = Var { name: "x".into(), ty: carrier.clone() };
    let y = Var { name: "y".into(), ty: carrier.clone() };
    let ix = Term::app(injection_const(inj, carrier.clone()), Term::var("x", carrier.clone()))
        .expect("injection on x");
    let iy = Term::app(injection_const(inj, carrier.clone()), Term::var("y", carrier))
        .expect("injection on y");
    let le_int = binop_const(INT_LE, int_ty(), int_ty(), Type::bool_());
    let body = Term::app(Term::app(le_int, ix).expect("Int.le ix"), iy).expect("Int.le ix iy");
    Term::lam(x, Term::lam(y, body))
}

fn partial_ord_instance(sort: &str) -> Instance {
    Instance::new(PARTIAL_ORD, vec![carrier_ty(sort)]).with_method(M_LE, le_body(sort))
}

fn ord_instance(sort: &str) -> Instance {
    let carrier = carrier_ty(sort);
    Instance::new(ORD, vec![carrier.clone()]).with_premise(Premise::new(PARTIAL_ORD, vec![carrier]))
}

/// `PartialIntegerLike(sort)` ground instance carrying the `domain` positivity
/// dictionary (and, for `Int`, the ring ops).
fn partial_instance(sort: &str) -> Instance {
    let carrier = carrier_ty(sort);
    let mut inst = Instance::new(PARTIAL_INTEGER_LIKE, vec![carrier.clone()])
        .with_method(M_DOMAIN, domain_body(sort));
    if sort == SORT_INT {
        inst = inst
            .with_method(
                M_ADD,
                binop_const(INT_ADD, carrier.clone(), carrier.clone(), carrier.clone()),
            )
            .with_method(M_MUL, binop_const(INT_MUL, carrier.clone(), carrier.clone(), carrier));
    }
    inst
}

/// `IntegerLike(sort)`: premises `PartialIntegerLike(sort)` and `Ord(sort)`.
fn integer_instance(sort: &str) -> Instance {
    let carrier = carrier_ty(sort);
    Instance::new(INTEGER_LIKE, vec![carrier.clone()])
        .with_premise(Premise::new(PARTIAL_INTEGER_LIKE, vec![carrier.clone()]))
        .with_premise(Premise::new(ORD, vec![carrier]))
}

/// `RealLike(Real)`: the field core `{add, mul, domain=⊤}`, with the order
/// supplied through its `PartialOrd(Real)` premise. (`Real` is a ring-complete
/// field, so `add`/`mul` are wired directly — unlike `Nat`/`WNat`, whose
/// carrier-valued ops await the `Reduces` spine.)
fn real_like_instance() -> Instance {
    let carrier = carrier_ty(SORT_REAL);
    Instance::new(REAL_LIKE, vec![carrier.clone()])
        .with_premise(Premise::new(PARTIAL_ORD, vec![carrier.clone()]))
        .with_method(M_ADD, binop_const(REAL_ADD, carrier.clone(), carrier.clone(), carrier.clone()))
        .with_method(M_MUL, binop_const(REAL_MUL, carrier.clone(), carrier.clone(), carrier.clone()))
        .with_method(M_DOMAIN, domain_body(SORT_REAL))
}

/// Build the `domain` body `λ(x : carrier). lo ≤ ι(x)`. For `Int` the injection
/// is the identity and there is no lower bound, so the body is `λx. ⊤`.
fn domain_body(sort: &str) -> Term {
    let carrier = carrier_ty(sort);
    let x = Var { name: "x".into(), ty: carrier.clone() };
    let xt = Term::Var(Arc::new(x.clone()));
    let body = match sort {
        // `Int` and `Real` are whole sorts (no carved-out validity predicate).
        SORT_INT | SORT_REAL => Term::true_const(),
        SORT_WNAT => positivity_guard(WNAT2INT, carrier, xt, 0),
        SORT_NAT => positivity_guard(NAT2INT, carrier, xt, 1),
        other => unreachable!("domain_body on non-carrier {other}"),
    };
    Term::lam(x, body)
}

/// `Int.le <lo> (inj x)` — the carrier's lower-bound positivity constraint over
/// its integer image.
fn positivity_guard(inj: &str, carrier: Type, xt: Term, lo: i128) -> Term {
    let img = Term::app(injection_const(inj, carrier), xt).expect("injection well-typed");
    let lo_lit = Term::const_(&lo.to_string(), int_ty());
    let le = binop_const(INT_LE, int_ty(), int_ty(), Type::bool_());
    let partial = Term::app(le, lo_lit).expect("Int.le on a literal");
    Term::app(partial, img).expect("Int.le on the image")
}

// ── installation ────────────────────────────────────────────────────────

const CARRIERS: [&str; 3] = [SORT_INT, SORT_NAT, SORT_WNAT];

fn declare_relations(db: &mut InstanceDb) {
    db.declare_relation(partial_ord());
    db.declare_relation(ord());
    db.declare_relation(partial_integer_like());
    db.declare_relation(integer_like());
    db.declare_relation(real_like());
}

/// Install the order + number relations and their ground instances
/// **structurally** (no law checking): the integer carriers `Int`/`Nat`/`WNat`
/// (`PartialOrd`/`Ord`/`PartialIntegerLike`/`IntegerLike`) and the field carrier
/// `Real` (`PartialOrd`/`Ord`/`RealLike`). Use when a consumer only needs
/// resolution; [`install_numberlike_checked`] adds proof-gated admission.
pub fn install_numberlike(db: &mut InstanceDb) {
    declare_relations(db);
    for sort in CARRIERS {
        db.declare_instance(partial_ord_instance(sort)).expect("PartialOrd instance");
        db.declare_instance(ord_instance(sort)).expect("Ord instance");
        db.declare_instance(partial_instance(sort)).expect("PartialIntegerLike instance");
        db.declare_instance(integer_instance(sort)).expect("IntegerLike instance");
    }
    // the field side: Real is PartialOrd + Ord (genuine total order) + RealLike.
    db.declare_instance(partial_ord_instance(SORT_REAL)).expect("PartialOrd(Real)");
    db.declare_instance(ord_instance(SORT_REAL)).expect("Ord(Real)");
    db.declare_instance(real_like_instance()).expect("RealLike(Real)");
}

/// Install the family with **proof-gated admission**: every instance must
/// discharge its relation's laws via `prover` or the declaration is rejected
/// (the user's "걸리는 인스턴스 선언은 아예 빌드 거부" gate). Superclasses are
/// admitted before subclasses so a subtrait law can resolve an inherited method
/// (`Ord`'s totality resolves `le` through the already-admitted `PartialOrd`).
pub fn install_numberlike_checked(
    db: &mut InstanceDb,
    prover: &dyn LawProver,
) -> Result<(), ClassError> {
    declare_relations(db);
    for sort in CARRIERS {
        db.declare_instance_lawful(partial_ord_instance(sort), prover)?;
        db.declare_instance_lawful(ord_instance(sort), prover)?;
        db.declare_instance_lawful(partial_instance(sort), prover)?;
        db.declare_instance_lawful(integer_instance(sort), prover)?;
    }
    // the field side: Real's order is proof-gated exactly like the integers'
    // (the prover discharges PartialOrd's reflexivity/antisymmetry/transitivity
    // + Ord's totality over `Real.le`, an LRA-decidable dense total order).
    db.declare_instance_lawful(partial_ord_instance(SORT_REAL), prover)?;
    db.declare_instance_lawful(ord_instance(SORT_REAL), prover)?;
    db.declare_instance_lawful(real_like_instance(), prover)?;
    Ok(())
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

    fn found(db: &InstanceDb, rel: &str, sort: &str) -> ResolutionResult {
        Resolver::new(db).resolve(&ClassGoal::new(rel, vec![carrier_ty(sort)]))
    }

    // ── hierarchy resolution ────────────────────────────────────────────

    #[test]
    fn integer_like_premises_partial_integer_like_and_ord() {
        let db = db();
        match found(&db, INTEGER_LIKE, SORT_INT) {
            ResolutionResult::Found(m) => {
                let rels: Vec<&str> = m.sub_goals.iter().map(|g| g.relation.as_str()).collect();
                assert_eq!(m.sub_goals.len(), 2, "two premises");
                assert!(rels.contains(&PARTIAL_INTEGER_LIKE));
                assert!(rels.contains(&ORD));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn ord_premises_partial_ord() {
        let db = db();
        match found(&db, ORD, SORT_INT) {
            ResolutionResult::Found(m) => {
                assert_eq!(m.sub_goals.len(), 1);
                assert_eq!(m.sub_goals[0].relation, PARTIAL_ORD);
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn partial_ord_resolves_without_subgoals() {
        let db = db();
        for sort in CARRIERS {
            match found(&db, PARTIAL_ORD, sort) {
                ResolutionResult::Found(m) => assert!(m.sub_goals.is_empty()),
                other => panic!("expected Found for {sort}, got {other:?}"),
            }
        }
    }

    #[test]
    fn all_three_carriers_are_integer_like() {
        let db = db();
        for sort in CARRIERS {
            assert!(matches!(found(&db, INTEGER_LIKE, sort), ResolutionResult::Found(_)));
        }
    }

    #[test]
    fn unregistered_carrier_is_not_found() {
        let db = db();
        let goal = ClassGoal::new(INTEGER_LIKE, vec![Type::bool_()]);
        assert!(matches!(Resolver::new(&db).resolve(&goal), ResolutionResult::NotFound));
    }

    // ── field axis (RealLike) ───────────────────────────────────────────

    #[test]
    fn real_like_resolves_with_a_partial_ord_premise() {
        let db = db();
        match found(&db, REAL_LIKE, SORT_REAL) {
            ResolutionResult::Found(m) => {
                assert_eq!(m.sub_goals.len(), 1, "RealLike premises PartialOrd");
                assert_eq!(m.sub_goals[0].relation, PARTIAL_ORD);
                assert_eq!(m.sub_goals[0].types[0], carrier_ty(SORT_REAL));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn real_is_ord_but_not_integer_like() {
        let db = db();
        // genuine Real has a total order (a separate Ord(Real) instance) …
        assert!(matches!(found(&db, ORD, SORT_REAL), ResolutionResult::Found(_)));
        // … but is NOT integer-like (no IntegerLike(Real) / PartialIntegerLike(Real)).
        assert!(matches!(found(&db, INTEGER_LIKE, SORT_REAL), ResolutionResult::NotFound));
        assert!(matches!(found(&db, PARTIAL_INTEGER_LIKE, SORT_REAL), ResolutionResult::NotFound));
    }

    #[test]
    fn real_le_is_native_and_domain_is_total() {
        // Real's `le` is the native `Real.le` (no injection wrapper) …
        let le = le_body(SORT_REAL);
        match le.kind() {
            TermInner::Const(c) => assert_eq!(c.name, REAL_LE),
            other => panic!("expected a bare Real.le const, got {other:?}"),
        }
        // … and its `domain` is the whole field (λx. ⊤).
        let dom = real_like_instance().methods.iter().find(|m| m.name == M_DOMAIN).unwrap().body.clone();
        match dom.kind() {
            TermInner::Lam(_, body) => assert!(body.is_true_const(), "Real domain is ⊤"),
            other => panic!("expected λ, got {other:?}"),
        }
    }

    // ── domain (positivity) dictionary ──────────────────────────────────

    #[test]
    fn nat_domain_is_the_positivity_predicate() {
        let inst = partial_instance(SORT_NAT);
        let domain = &inst.methods.iter().find(|m| m.name == M_DOMAIN).unwrap().body;
        match domain.kind() {
            TermInner::Lam(v, body) => {
                assert_eq!(v.ty, carrier_ty(SORT_NAT));
                assert_eq!(body.type_of(), Type::bool_());
                let s = format!("{body:?}");
                assert!(s.contains(NAT2INT) && s.contains(INT_LE), "Nat ≥ 1 via nat2int: {s}");
            }
            other => panic!("expected λ domain body, got {other:?}"),
        }
    }

    #[test]
    fn wnat_lower_bound_is_zero_nat_is_one() {
        let wnat = format!("{:?}", partial_instance(SORT_WNAT).methods[0].body);
        let nat = format!("{:?}", partial_instance(SORT_NAT).methods[0].body);
        assert!(wnat.contains(WNAT2INT) && wnat.contains("\"0\""), "WNat ≥ 0: {wnat}");
        assert!(nat.contains(NAT2INT) && nat.contains("\"1\""), "Nat ≥ 1: {nat}");
    }

    #[test]
    fn int_domain_is_trivially_true() {
        let inst = partial_instance(SORT_INT);
        let domain = &inst.methods.iter().find(|m| m.name == M_DOMAIN).unwrap().body;
        match domain.kind() {
            TermInner::Lam(_, body) => assert!(body.is_true_const()),
            other => panic!("expected λ, got {other:?}"),
        }
    }

    // ── law obligations ─────────────────────────────────────────────────

    /// A self-contained dictionary view, for exercising a law builder directly.
    struct TestDict {
        carrier: Type,
        methods: Vec<(String, Term)>,
    }
    impl Dict for TestDict {
        fn carriers(&self) -> &[Type] {
            std::slice::from_ref(&self.carrier)
        }
        fn method(&self, name: &str) -> Option<Term> {
            self.methods.iter().find(|(n, _)| n == name).map(|(_, t)| t.clone())
        }
    }

    #[test]
    fn totality_obligation_is_well_typed_int_le_disjunction() {
        let dict = TestDict {
            carrier: int_ty(),
            methods: vec![(M_LE.into(), le_body(SORT_INT))],
        };
        let goal = law_totality(&dict).expect("build totality");
        assert_eq!(goal.type_of(), Type::bool_(), "obligation is a Bool prop");
        // ∀a. ∀b. (Int.le a b) ∨ (Int.le b a)
        let (_, b1) = goal.dest_forall().expect("outer ∀");
        let (_, inner) = b1.dest_forall().expect("inner ∀");
        let (l, r) = inner.dest_or().expect("disjunction");
        assert!(is_int_le_app(&l) && is_int_le_app(&r), "both sides are Int.le applications");
    }

    #[test]
    fn injected_le_obligation_beta_reduces_to_a_clean_atom() {
        // Nat's le is λa b. Int.le (nat2int a) (nat2int b); the reflexivity
        // obligation must β-reduce to ∀a. Int.le (nat2int a) (nat2int a).
        let dict = TestDict {
            carrier: carrier_ty(SORT_NAT),
            methods: vec![(M_LE.into(), le_body(SORT_NAT))],
        };
        let goal = law_reflexivity(&dict).expect("build reflexivity");
        let (_, body) = goal.dest_forall().expect("∀a");
        assert!(is_int_le_app(&body), "β-reduced to a bare Int.le app: {body:?}");
        let s = format!("{body:?}");
        assert!(s.contains(NAT2INT), "still routes through nat2int: {s}");
    }

    fn is_int_le_app(t: &Term) -> bool {
        if let TermInner::App(f, _) = t.kind()
            && let TermInner::App(g, _) = f.kind()
            && let TermInner::Const(c) = g.kind()
        {
            return c.name == INT_LE;
        }
        false
    }

    // ── proof-gated admission ───────────────────────────────────────────

    struct AlwaysValid;
    impl LawProver for AlwaysValid {
        fn prove_valid(&self, _: &Term) -> bool {
            true
        }
    }
    struct NeverValid;
    impl LawProver for NeverValid {
        fn prove_valid(&self, _: &Term) -> bool {
            false
        }
    }
    /// Proves exactly the standard-integer-order totality shape valid.
    struct TotalityRecognizer;
    impl LawProver for TotalityRecognizer {
        fn prove_valid(&self, goal: &Term) -> bool {
            // ∀a. ∀b. (Int.le a b) ∨ (Int.le b a)
            let Some((_, b1)) = goal.dest_forall() else { return false };
            let Some((_, inner)) = b1.dest_forall() else { return false };
            let Some((l, r)) = inner.dest_or() else { return false };
            is_int_le_app(&l) && is_int_le_app(&r)
        }
    }

    #[test]
    fn lawful_install_succeeds_with_a_capable_prover() {
        let mut db = InstanceDb::new();
        install_numberlike_checked(&mut db, &AlwaysValid).expect("admitted");
        assert!(matches!(found(&db, INTEGER_LIKE, SORT_INT), ResolutionResult::Found(_)));
    }

    #[test]
    fn lawful_install_rejects_when_a_law_is_unproven() {
        let mut db = InstanceDb::new();
        let err = install_numberlike_checked(&mut db, &NeverValid).unwrap_err();
        match err {
            ClassError::LawUnproven { relation, law } => {
                // The first declared law-bearing instance is PartialOrd; its
                // first law is reflexivity.
                assert_eq!(relation, PARTIAL_ORD);
                assert_eq!(law, "reflexivity");
            }
            other => panic!("expected LawUnproven, got {other:?}"),
        }
    }

    #[test]
    fn totality_gate_admits_a_total_order_and_rejects_a_non_total_one() {
        // Int.le is total → Ord(Int) admitted.
        let mut db = InstanceDb::new();
        db.declare_relation(partial_ord());
        db.declare_relation(ord());
        db.declare_instance(partial_ord_instance(SORT_INT)).unwrap();
        assert!(
            db.declare_instance_lawful(ord_instance(SORT_INT), &TotalityRecognizer).is_ok(),
            "Int is a total order → Ord(Int) admitted",
        );

        // A foreign carrier whose `le` the recognizer does not accept as total
        // → Ord(Foo) build-rejected on the totality law.
        let foo = Type::const_("Foo", Kind::Type);
        let foo_le = binop_const("Foo.le", foo.clone(), foo.clone(), Type::bool_());
        db.declare_instance(
            Instance::new(PARTIAL_ORD, vec![foo.clone()]).with_method(M_LE, foo_le),
        )
        .unwrap();
        let bogus = Instance::new(ORD, vec![foo.clone()])
            .with_premise(Premise::new(PARTIAL_ORD, vec![foo]));
        match db.declare_instance_lawful(bogus, &TotalityRecognizer) {
            Err(ClassError::LawUnproven { relation, law }) => {
                assert_eq!(relation, ORD);
                assert_eq!(law, "totality");
            }
            other => panic!("expected totality rejection, got {other:?}"),
        }
    }

    #[test]
    fn ord_totality_resolves_le_through_the_partial_ord_premise() {
        // Ord(Int) carries no `le` of its own; the totality obligation must
        // still build by resolving `le` through the PartialOrd(Int) premise.
        // A capable prover therefore admits it; AlwaysValid suffices to show
        // the obligation *built* (LawIllFormed would fire first otherwise).
        let mut db = InstanceDb::new();
        db.declare_relation(partial_ord());
        db.declare_relation(ord());
        db.declare_instance(partial_ord_instance(SORT_INT)).unwrap();
        assert!(db.declare_instance_lawful(ord_instance(SORT_INT), &TotalityRecognizer).is_ok());
    }
}
