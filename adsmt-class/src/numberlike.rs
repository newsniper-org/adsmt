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
//!   ℤ, ℕ, WNat are `IntegerLike`; its sibling [`complex_integer_like`]
//!   (`ComplexIntegerLike`, ℤ[i]/ℤ[ω]) is integer-like-extension but **not**
//!   `Ord` (no total order on ℂ — the extension axis below).
//!
//! **Field axis** (the scalar-field sibling of the integer axis):
//! * [`real_like`] — `RealLike(R)`: a field-like carrier `{add, mul, domain}`
//!   whose order is supplied through its instance's `PartialOrd(R)` premise. The
//!   genuine `Real` is additionally declared `Ord(Real)` (a separate instance,
//!   not a `RealLike` premise) — a `FloatingPoint` carrier would be `RealLike` +
//!   `PartialOrd` but **not** `Ord` (`NaN` breaks totality). `Real`'s `le` is the
//!   native `Real.le` (LRA) and its `domain` is the whole field (`λx. ⊤`).
//!
//! **Extension axis** (degree-2 ring/field extensions, the `Pair`-rep minpoly
//! members):
//! * [`complex_integer_like`] — `ComplexIntegerLike(C, B)`: the integer-side
//!   degree-2 ring extension `C = a + bζ` of an `IntegerLike` base `B`, ζ a root
//!   of an imaginary-quadratic monic minpoly `x²+c1·x+c0`. A sibling of
//!   `IntegerLike` under `PartialIntegerLike` — adds the complex-generator
//!   structure, **no** `Ord` premise (G4: ℂ has no total order). Instances ℤ[i]
//!   (`x²+1`) and ℤ[ω] (`x²+x+1`).
//! * [`complex_like`] — `ComplexLike(C, B)`: the field-side mirror over a
//!   `RealLike` base (instance ℂ = ℝ[i]). Differs from `ComplexIntegerLike` only
//!   in the coefficient base (`RealLike` vs `IntegerLike`) and the routed theory
//!   (NRA vs NIA).
//!
//!   Both extension relations are admitted through [`declare_complex_instance`],
//!   the **G1 irreducibility gate** — a degree-2 minpoly is admitted only if its
//!   discriminant `c1²−4c0 < 0` (imaginary-quadratic ⟹ irreducible ⟹ no zero
//!   divisors; a reducible minpoly would admit a spurious unsat), plus the **G6**
//!   ring-complete-base check. The reduction-algebra method bodies
//!   (`add`/`mul`/`norm`) are `Reduces`-spine-deferred (G2 — NIA/NRA-abstaining
//!   until oxiz-nl2 is on the polite bus); the soundness-critical algebra is
//!   Verus-pre-verified (`~/complexlike-verification`).
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
/// `ComplexIntegerLike(C, B)` — the integer-side degree-2 ring **extension** of a
/// base `IntegerLike(B)`: a carrier `C = a + bζ` whose generator `ζ` is a root of
/// an imaginary-quadratic monic minpoly `x² + c1·x + c0` (discriminant
/// `c1²−4c0 < 0`). A **sibling of `IntegerLike` under `PartialIntegerLike`** that
/// adds the complex-generator structure instead of a total order: it premises the
/// base ring through `IntegerLike(B)` but carries **no `Ord` premise** (G4 — no
/// total order on ℂ). Instances: **ℤ[i]** Gaussian (`x²+1`, `c0=1,c1=0`,
/// disc=−4), **ℤ[ω]** Eisenstein (`x²+x+1`, `c0=1,c1=1`, disc=−3). The minpoly
/// coefficients are static instance data gating admission ([`declare_complex_instance`]:
/// the **G1** irreducibility gate — a reducible degree-2 minpoly has zero divisors
/// and would admit a spurious unsat).
pub const COMPLEX_INTEGER_LIKE: &str = "ComplexIntegerLike";
/// `ComplexLike(C, B)` — the field-side mirror of `ComplexIntegerLike`: the
/// degree-2 field **extension** of a base `RealLike(B)`. Same `Pair`-rep + minpoly
/// structure; differs only in the coefficient base (`RealLike` vs `IntegerLike`)
/// and the theory the reduction routes to (NRA vs NIA). Instance **ℂ = ℝ[i]**
/// (`x²+1`, disc=−4). **No order at all** (G4 — `<≤>≥` are rejected at
/// elaboration). Admitted through the same G1 discriminant gate.
pub const COMPLEX_LIKE: &str = "ComplexLike";

// ── method names ────────────────────────────────────────────────────────
/// Order `I -> I -> Bool` (lives on `PartialOrd`).
pub const M_LE: &str = "le";
/// In-carrier validity / positivity predicate `I -> Bool`.
pub const M_DOMAIN: &str = "domain";
/// Carrier addition `I -> I -> I`.
pub const M_ADD: &str = "add";
/// Carrier multiplication `I -> I -> I`.
pub const M_MUL: &str = "mul";
/// The extension **norm** `C -> B` (`N(a+bζ) = a² − c1·ab + c0·b²`, the
/// minpoly-derived field norm). Lives on the `Complex*Like` extensions; maps a
/// carrier element to its base-ring norm. Body is `Reduces`-spine-deferred (G2 —
/// NIA/NRA-abstaining until oxiz-nl2 is on the polite bus).
pub const M_NORM: &str = "norm";

// ── carrier sort + engine op names ──────────────────────────────────────
//
// Mirrored by value from `adsmt_ir::theory`. `adsmt-class` sits below
// `adsmt-ir` and must not depend on it; the lowering slice that consumes these
// dictionaries matches against the same names.
const SORT_INT: &str = "Int";
const SORT_NAT: &str = "Nat";
const SORT_WNAT: &str = "WNat";
const SORT_REAL: &str = "Real";
/// ℤ[i] — the Gaussian integers (`x²+1`, disc=−4), a `ComplexIntegerLike` carrier.
const SORT_GAUSSIAN: &str = "GaussianInt";
/// ℤ[ω] — the Eisenstein integers (`x²+x+1`, disc=−3), a `ComplexIntegerLike` carrier.
const SORT_EISENSTEIN: &str = "EisensteinInt";
/// ℂ = ℝ[i] (`x²+1`, disc=−4), the `ComplexLike` field carrier.
const SORT_COMPLEX: &str = "Complex";

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
    // 2-param heterogeneous form (owner reshape, 2026-07-03 — see
    // docs/design/EQ_ORD_UPCAST_RELATIONS.md): `PartialOrd(T, A)` inherits
    // `PartialEq(T, A)` AND `UpCast(T, A)` (instance premises) — a cross-sort
    // comparison is decided in the upcast target. The laws are stated on the
    // diagonal (every current instance is diagonal).
    let t = tyvar("T");
    let a = tyvar("A");
    let (tt, at) = (Type::Var(t.clone()), Type::Var(a.clone()));
    Relation::new(PARTIAL_ORD)
        .with_param(t)
        .with_param(a)
        .with_method(M_LE, fun3(tt, at, Type::bool_()))
        .with_law(Law::new("reflexivity", law_reflexivity))
        .with_law(Law::new("antisymmetry", law_antisymmetry))
        .with_law(Law::new("transitivity", law_transitivity))
}

/// `Ord(T) : PartialOrd(T, T), Eq(T)`: the total-order subtrait. Adds the
/// totality law and no new method (`le` is inherited through the diagonal
/// `PartialOrd` premise; equality through `Eq`).
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

/// A degree-2 ring/field **extension** relation `Ext(C, B)`: a carrier `C` over a
/// base `B`, with the ring core `{add, mul}` (carrier-valued) and the
/// minpoly-derived `norm : C -> B` (base-valued). `[C] → [B]` is a functional
/// dependency (the carrier determines its base). **No order laws** — the
/// `Complex*Like` extensions are unordered (G4); the order axis lives entirely on
/// `PartialOrd`/`Ord`, which these never premise.
fn extension_relation(name: &str) -> Relation {
    let c = tyvar("C");
    let b = tyvar("B");
    let ct = Type::Var(c.clone());
    let bt = Type::Var(b.clone());
    Relation::new(name)
        .with_param(c)
        .with_param(b)
        .with_fundep(crate::fundep::Fundep::new(vec![0], vec![1]))
        .with_method(M_ADD, fun3(ct.clone(), ct.clone(), ct.clone()))
        .with_method(M_MUL, fun3(ct.clone(), ct.clone(), ct.clone()))
        .with_method(M_NORM, Type::fun(ct, bt).expect("kind"))
}

/// `ComplexIntegerLike(C, B)`: the integer-side degree-2 ring extension (ℤ[i],
/// ℤ[ω] over an `IntegerLike` base). A sibling of `IntegerLike` under
/// `PartialIntegerLike` — adds the complex-generator structure, never a total
/// order (G4 — no `Ord` premise).
pub fn complex_integer_like() -> Relation {
    extension_relation(COMPLEX_INTEGER_LIKE)
}

/// `ComplexLike(C, B)`: the field-side degree-2 extension (ℂ = ℝ[i] over a
/// `RealLike` base). The field mirror of `ComplexIntegerLike`; no order at all.
pub fn complex_like() -> Relation {
    extension_relation(COMPLEX_LIKE)
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
pub(crate) fn app_beta(f: Term, x: Term) -> Result<Term, LawError> {
    let applied = Term::app(f, x)?;
    Ok(applied.beta_reduce().unwrap_or(applied))
}

/// `f x y`, β-reduced.
pub(crate) fn apply2(f: &Term, x: Term, y: Term) -> Result<Term, LawError> {
    app_beta(app_beta(f.clone(), x)?, y)
}

/// Universally close `body` over `names`, each a binder of carrier sort.
pub(crate) fn close_forall(carrier: &Type, names: &[&str], body: Term) -> Result<Term, LawError> {
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
    // Diagonal `PartialOrd(T, T)` with the inherited premises: `PartialEq(T, T)`
    // (through the carrier's `Eq`) and `UpCast(T, T)` (the builtin identity —
    // stored as a premise, satisfied at resolution; an explicit instance would
    // be rejected).
    let c = carrier_ty(sort);
    Instance::new(PARTIAL_ORD, vec![c.clone(), c.clone()])
        .with_premise(Premise::new(crate::eq_ord::PARTIAL_EQ, vec![c.clone(), c.clone()]))
        .with_premise(Premise::new(crate::eq_ord::UP_CAST, vec![c.clone(), c]))
        .with_method(M_LE, le_body(sort))
}

fn ord_instance(sort: &str) -> Instance {
    let carrier = carrier_ty(sort);
    Instance::new(ORD, vec![carrier.clone()])
        .with_premise(Premise::new(PARTIAL_ORD, vec![carrier.clone(), carrier.clone()]))
        .with_premise(Premise::new(crate::eq_ord::EQ, vec![carrier]))
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
/// supplied through its diagonal `PartialOrd(Real, Real)` premise. (`Real` is a ring-complete
/// field, so `add`/`mul` are wired directly — unlike `Nat`/`WNat`, whose
/// carrier-valued ops await the `Reduces` spine.)
fn real_like_instance() -> Instance {
    let carrier = carrier_ty(SORT_REAL);
    Instance::new(REAL_LIKE, vec![carrier.clone()])
        .with_premise(Premise::new(PARTIAL_ORD, vec![carrier.clone(), carrier.clone()]))
        .with_method(M_ADD, binop_const(REAL_ADD, carrier.clone(), carrier.clone(), carrier.clone()))
        .with_method(M_MUL, binop_const(REAL_MUL, carrier.clone(), carrier.clone(), carrier.clone()))
        .with_method(M_DOMAIN, domain_body(SORT_REAL))
}

/// A `Complex*Like` extension instance over `(carrier, base)` premising the base
/// `*Like` relation. The reduction-algebra method bodies (`add`/`mul`/`norm`) are
/// **deferred** (G2 — the `Reduces` spine routes to NIA/NRA, which abstain until
/// oxiz-nl2 is on the polite bus): the instance carries the base premise and its
/// minpoly is supplied to [`declare_complex_instance`] as the admission datum.
fn extension_instance(relation: &str, carrier: &str, base_relation: &str, base: &str) -> Instance {
    Instance::new(relation, vec![carrier_ty(carrier), carrier_ty(base)])
        .with_premise(Premise::new(base_relation, vec![carrier_ty(base)]))
}

/// ℤ[i] — `ComplexIntegerLike(GaussianInt, Int)` over `IntegerLike(Int)`,
/// minpoly `x²+1` (`c0=1, c1=0`, disc=−4).
fn gaussian_instance() -> Instance {
    extension_instance(COMPLEX_INTEGER_LIKE, SORT_GAUSSIAN, INTEGER_LIKE, SORT_INT)
}

/// ℤ[ω] — `ComplexIntegerLike(EisensteinInt, Int)` over `IntegerLike(Int)`,
/// minpoly `x²+x+1` (`c0=1, c1=1`, disc=−3).
fn eisenstein_instance() -> Instance {
    extension_instance(COMPLEX_INTEGER_LIKE, SORT_EISENSTEIN, INTEGER_LIKE, SORT_INT)
}

/// ℂ — `ComplexLike(Complex, Real)` over `RealLike(Real)`, minpoly `x²+1`
/// (`c0=1, c1=0`, disc=−4).
fn complex_instance() -> Instance {
    extension_instance(COMPLEX_LIKE, SORT_COMPLEX, REAL_LIKE, SORT_REAL)
}

/// The lower-bound-free sort name of a carrier type (for diagnostics / the G6
/// base-ring check). Non-`Const` types report `"?"`.
fn sort_name(ty: &Type) -> String {
    match ty {
        Type::Const(c) => c.name.clone(),
        other => format!("{other:?}"),
    }
}

/// Admit a `Complex*Like` extension instance behind the soundness gates that the
/// reduction algebra depends on (선검증 `~/complexlike-verification`):
///
/// * **G1 — minpoly irreducibility.** The generator's monic minpoly `x² + c1·x +
///   c0` must be *irreducible* over the base, i.e. imaginary-quadratic
///   (discriminant `c1²−4c0 < 0`). A reducible degree-2 minpoly factors, so the
///   extension has **zero divisors** (`ζ−r` and `ζ−s` multiply to 0 with neither
///   factor 0) — and the verified `no_zero_divisors`/`norm_positive_definite`
///   lemmas (`N=0 ⟺ a=b=0`, `4N=(2a−c1b)²+(−disc)b²`) would no longer hold, so a
///   ground equation could be reduced to a false `0 = nonzero` → **spurious
///   unsat**. Rejected as [`ClassError::ReducibleMinpoly`].
/// * **G6 — ring-complete base.** The base must be subtraction-closed (a genuine
///   ring): the reduction `(a,b)·(c,d) = (ac−c0bd, …)` produces base
///   *differences*, so a non-ring base (`Nat`/`WNat`, no negatives) makes the
///   encode/decode partial → unsound. Rejected as [`ClassError::NonRingBase`].
///
/// On success the instance is declared exactly as [`InstanceDb::declare_instance`]
/// (structural arity/coherence still apply). The minpoly `(c0, c1)` is the static
/// admission datum (G8 — instance data, not a kernel `Poly` term); the z3
/// differential of the reduction on concrete values runs at the solver-routing
/// slice (G2-deferred here).
pub fn declare_complex_instance(
    db: &mut InstanceDb,
    inst: Instance,
    c0: i128,
    c1: i128,
) -> Result<(), ClassError> {
    let carrier = sort_name(&inst.types[0]);
    // G1: the discriminant must be strictly negative (irreducible quadratic).
    let disc = c1.checked_mul(c1).and_then(|s| s.checked_sub(4i128.checked_mul(c0)?));
    match disc {
        Some(d) if d < 0 => {}
        Some(d) => return Err(ClassError::ReducibleMinpoly { carrier, c0, c1, disc: d }),
        // An overflow can only arise from absurdly large coeffs; treat as
        // non-admissible rather than silently wrapping (conservative).
        None => return Err(ClassError::ReducibleMinpoly { carrier, c0, c1, disc: i128::MAX }),
    }
    // G6: the base (second head type) must be a ring-complete carrier — not a
    // subtraction-open refinement (`Nat`/`WNat`).
    let base = sort_name(inst.types.get(1).unwrap_or(&inst.types[0]));
    if base == SORT_NAT || base == SORT_WNAT {
        return Err(ClassError::NonRingBase { carrier, base });
    }
    db.declare_instance(inst)
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
    // the equality/cast half of the family (PartialEq / Eq / UpCast) — the
    // reshaped PartialOrd/Ord premise-chain bottoms out on it.
    crate::eq_ord::declare_eq_ord_relations(db);
    db.declare_relation(partial_ord());
    db.declare_relation(ord());
    db.declare_relation(partial_integer_like());
    db.declare_relation(integer_like());
    db.declare_relation(real_like());
    db.declare_relation(complex_integer_like());
    db.declare_relation(complex_like());
}

/// The three `Complex*Like` ground instances paired with their monic minpoly
/// `(c0, c1)` (`x² + c1·x + c0`) — the admission datum for [`declare_complex_instance`]'s
/// G1 discriminant gate: ℤ[i] (`x²+1`, disc=−4), ℤ[ω] (`x²+x+1`, disc=−3),
/// ℂ (`x²+1`, disc=−4). All three are imaginary-quadratic, so G1 admits them.
fn complex_instances() -> [(Instance, i128, i128); 3] {
    [
        (gaussian_instance(), 1, 0),
        (eisenstein_instance(), 1, 1),
        (complex_instance(), 1, 0),
    ]
}

/// Install the order + number relations and their ground instances
/// **structurally** (no law checking): the integer carriers `Int`/`Nat`/`WNat`
/// (`PartialOrd`/`Ord`/`PartialIntegerLike`/`IntegerLike`) and the field carrier
/// `Real` (`PartialOrd`/`Ord`/`RealLike`). Use when a consumer only needs
/// resolution; [`install_numberlike_checked`] adds proof-gated admission.
pub fn install_numberlike(db: &mut InstanceDb) {
    declare_relations(db);
    // diagonal PartialEq/Eq + the numeric UpCast lattice, BEFORE the ord
    // instances whose premise chains reference them.
    crate::eq_ord::install_eq_ord_numeric(db);
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
    // the extension members: ℤ[i]/ℤ[ω] (ComplexIntegerLike) + ℂ (ComplexLike),
    // each behind the G1 discriminant gate (all three are imaginary-quadratic).
    for (inst, c0, c1) in complex_instances() {
        declare_complex_instance(db, inst, c0, c1).expect("imaginary-quadratic minpoly admits");
    }
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
    // The extension members carry no order laws (G4 — no `Ord` premise); their
    // soundness gate is the *decidable* G1 discriminant check, not an engine
    // obligation, so admission goes through `declare_complex_instance` on both
    // the structural and proof-gated paths.
    for (inst, c0, c1) in complex_instances() {
        declare_complex_instance(db, inst, c0, c1)?;
    }
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
    fn ord_premises_partial_ord_and_eq() {
        // the reshaped hierarchy: Ord(T) : PartialOrd(T, T), Eq(T).
        let db = db();
        match found(&db, ORD, SORT_INT) {
            ResolutionResult::Found(m) => {
                let rels: Vec<&str> = m.sub_goals.iter().map(|g| g.relation.as_str()).collect();
                assert_eq!(m.sub_goals.len(), 2, "PartialOrd diag + Eq");
                assert!(rels.contains(&PARTIAL_ORD));
                assert!(rels.contains(&crate::eq_ord::EQ));
                let po = m.sub_goals.iter().find(|g| g.relation == PARTIAL_ORD).unwrap();
                assert_eq!(po.types.len(), 2, "diagonal 2-param PartialOrd");
                assert_eq!(po.types[0], po.types[1]);
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn partial_ord_diagonal_premises_partial_eq_and_upcast() {
        // PartialOrd(T, A) : PartialEq(T, A), UpCast(T, A) — on the diagonal
        // the UpCast premise is the builtin identity (resolves subgoal-free).
        let db = db();
        let r = Resolver::new(&db);
        for sort in CARRIERS {
            let c = carrier_ty(sort);
            let goal = ClassGoal::new(PARTIAL_ORD, vec![c.clone(), c.clone()]);
            match r.resolve(&goal) {
                ResolutionResult::Found(m) => {
                    let rels: Vec<&str> =
                        m.sub_goals.iter().map(|g| g.relation.as_str()).collect();
                    assert!(rels.contains(&crate::eq_ord::PARTIAL_EQ), "{sort}");
                    assert!(rels.contains(&crate::eq_ord::UP_CAST), "{sort}");
                    let up = m.sub_goals.iter().find(|g| g.relation == crate::eq_ord::UP_CAST).unwrap();
                    assert!(matches!(
                        r.resolve(up),
                        ResolutionResult::Found(ref im) if im.sub_goals.is_empty()
                    ), "identity UpCast is the builtin: {sort}");
                }
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

    // ── extension axis (ComplexIntegerLike / ComplexLike) ────────────────

    fn found2(db: &InstanceDb, rel: &str, c: &str, b: &str) -> ResolutionResult {
        Resolver::new(db).resolve(&ClassGoal::new(rel, vec![carrier_ty(c), carrier_ty(b)]))
    }

    #[test]
    fn gaussian_and_eisenstein_are_complex_integer_like_over_an_integer_base() {
        let db = db();
        for carrier in [SORT_GAUSSIAN, SORT_EISENSTEIN] {
            match found2(&db, COMPLEX_INTEGER_LIKE, carrier, SORT_INT) {
                ResolutionResult::Found(m) => {
                    assert_eq!(m.sub_goals.len(), 1, "premises the base ring");
                    assert_eq!(m.sub_goals[0].relation, INTEGER_LIKE, "{carrier} base is IntegerLike");
                    assert_eq!(m.sub_goals[0].types[0], carrier_ty(SORT_INT));
                }
                other => panic!("expected Found for {carrier}, got {other:?}"),
            }
        }
    }

    #[test]
    fn complex_is_complex_like_over_a_real_base() {
        let db = db();
        match found2(&db, COMPLEX_LIKE, SORT_COMPLEX, SORT_REAL) {
            ResolutionResult::Found(m) => {
                assert_eq!(m.sub_goals.len(), 1);
                assert_eq!(m.sub_goals[0].relation, REAL_LIKE, "ℂ base is RealLike");
                assert_eq!(m.sub_goals[0].types[0], carrier_ty(SORT_REAL));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn the_extension_carriers_have_no_order_and_are_not_integer_like() {
        // G4: ℤ[i]/ℤ[ω]/ℂ are unordered — no Ord/PartialOrd/IntegerLike instance.
        let db = db();
        for carrier in [SORT_GAUSSIAN, SORT_EISENSTEIN, SORT_COMPLEX] {
            assert!(matches!(found(&db, ORD, carrier), ResolutionResult::NotFound), "{carrier} not Ord");
            assert!(
                matches!(found(&db, PARTIAL_ORD, carrier), ResolutionResult::NotFound),
                "{carrier} not PartialOrd",
            );
            assert!(
                matches!(found(&db, INTEGER_LIKE, carrier), ResolutionResult::NotFound),
                "{carrier} not IntegerLike",
            );
        }
    }

    #[test]
    fn the_extension_norm_maps_the_carrier_to_its_base() {
        // The extension relation's `norm` signature is `C -> B` (carrier → base).
        for rel in [complex_integer_like(), complex_like()] {
            let norm = rel.methods.iter().find(|m| m.name == M_NORM).expect("has norm");
            let (dom, cod) = norm.signature.dest_fun().expect("norm is an arrow");
            assert_eq!(dom, Type::Var(rel.params[0].clone()), "norm domain is the carrier C");
            assert_eq!(cod, Type::Var(rel.params[1].clone()), "norm codomain is the base B");
            // add/mul stay carrier-valued endofunctions C -> C -> C.
            for op in [M_ADD, M_MUL] {
                let sig = &rel.methods.iter().find(|m| m.name == op).unwrap().signature;
                let (_, rest) = sig.dest_fun().unwrap();
                let (_, out) = rest.dest_fun().unwrap();
                assert_eq!(out, Type::Var(rel.params[0].clone()), "{op} is C -> C -> C");
            }
        }
    }

    // ── G1 irreducibility gate + G6 ring-complete base ───────────────────

    /// A db with the relations declared but no instances — for exercising the
    /// admission gate directly.
    fn empty_db() -> InstanceDb {
        let mut db = InstanceDb::new();
        declare_relations(&mut db);
        db
    }

    #[test]
    fn g1_admits_the_three_imaginary_quadratic_minpolys() {
        // disc = c1²−4c0 < 0 for all three: ℤ[i] −4, ℤ[ω] −3, ℂ −4.
        for (inst, c0, c1) in complex_instances() {
            let mut db = empty_db();
            assert!(
                declare_complex_instance(&mut db, inst, c0, c1).is_ok(),
                "imaginary-quadratic (disc {} < 0) admits",
                c1 * c1 - 4 * c0,
            );
        }
    }

    #[test]
    fn g1_rejects_a_reducible_minpoly() {
        // x²−1 (c0=−1, c1=0) factors as (x−1)(x+1): disc = 0−4·(−1) = 4 ≥ 0 →
        // reducible → zero divisors → would admit a spurious unsat. HARD-rejected.
        let mut db = empty_db();
        let synthetic =
            Instance::new(COMPLEX_INTEGER_LIKE, vec![carrier_ty("Hyperbolic"), carrier_ty(SORT_INT)])
                .with_premise(Premise::new(INTEGER_LIKE, vec![carrier_ty(SORT_INT)]));
        match declare_complex_instance(&mut db, synthetic, -1, 0) {
            Err(ClassError::ReducibleMinpoly { carrier, c0, c1, disc }) => {
                assert_eq!(carrier, "Hyperbolic");
                assert_eq!((c0, c1, disc), (-1, 0, 4));
            }
            other => panic!("expected ReducibleMinpoly, got {other:?}"),
        }
        // … and nothing was declared.
        assert!(matches!(
            found2(&db, COMPLEX_INTEGER_LIKE, "Hyperbolic", SORT_INT),
            ResolutionResult::NotFound,
        ));
    }

    #[test]
    fn g1_rejects_a_repeated_root_minpoly_disc_zero() {
        // x² (c0=0, c1=0): disc = 0 ≥ 0 — a repeated root ζ=0, the degenerate
        // reducible case. Rejected (the gate is strict `< 0`).
        let mut db = empty_db();
        let degenerate =
            Instance::new(COMPLEX_LIKE, vec![carrier_ty("Dual"), carrier_ty(SORT_REAL)])
                .with_premise(Premise::new(REAL_LIKE, vec![carrier_ty(SORT_REAL)]));
        assert!(matches!(
            declare_complex_instance(&mut db, degenerate, 0, 0),
            Err(ClassError::ReducibleMinpoly { disc: 0, .. }),
        ));
    }

    #[test]
    fn g6_rejects_a_non_ring_base() {
        // A degree-2 extension over Nat (no subtraction) is rejected even with an
        // irreducible minpoly — the reduction's base differences escape ℕ.
        let mut db = empty_db();
        // declare a PartialIntegerLike(Nat) so the premise *could* resolve; the
        // G6 gate must still reject on the base sort, before resolution matters.
        db.declare_relation(integer_like());
        let bad_base =
            Instance::new(COMPLEX_INTEGER_LIKE, vec![carrier_ty("GaussianNat"), carrier_ty(SORT_NAT)])
                .with_premise(Premise::new(INTEGER_LIKE, vec![carrier_ty(SORT_NAT)]));
        match declare_complex_instance(&mut db, bad_base, 1, 0) {
            Err(ClassError::NonRingBase { carrier, base }) => {
                assert_eq!(carrier, "GaussianNat");
                assert_eq!(base, SORT_NAT);
            }
            other => panic!("expected NonRingBase, got {other:?}"),
        }
    }

    #[test]
    fn lawful_install_admits_the_extension_members_through_g1() {
        // install_numberlike_checked routes the extensions through the same G1
        // gate; a capable order-prover suffices since the extensions carry no
        // order laws of their own.
        let mut db = InstanceDb::new();
        install_numberlike_checked(&mut db, &AlwaysValid).expect("admitted");
        assert!(matches!(
            found2(&db, COMPLEX_INTEGER_LIKE, SORT_GAUSSIAN, SORT_INT),
            ResolutionResult::Found(_),
        ));
        assert!(matches!(
            found2(&db, COMPLEX_LIKE, SORT_COMPLEX, SORT_REAL),
            ResolutionResult::Found(_),
        ));
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
            Instance::new(PARTIAL_ORD, vec![foo.clone(), foo.clone()]).with_method(M_LE, foo_le),
        )
        .unwrap();
        let bogus = Instance::new(ORD, vec![foo.clone()])
            .with_premise(Premise::new(PARTIAL_ORD, vec![foo.clone(), foo]));
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
