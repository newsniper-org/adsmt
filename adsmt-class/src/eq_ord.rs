//! The `PartialEq` / `Eq` / `UpCast` relation family — the equality/cast half
//! of the owner-specified hierarchy (docs/design/EQ_ORD_UPCAST_RELATIONS.md;
//! the order half `PartialOrd(T,A)`/`Ord(T)` lives in [`crate::numberlike`],
//! reshaped onto this family):
//!
//! * [`partial_eq`] — `PartialEq(A, B)`: heterogeneous equality. Declaring an
//!   instance with `A ≠ B` IMPLICITLY synchronizes the mirror
//!   `PartialEq(B, A)` (the registry materializes it; an explicit mirror is a
//!   duplicate-instance coherence error). See `InstanceDb::declare_instance`.
//! * [`eq`] — `Eq(T) : PartialEq(T, T)`: total equality on one sort. No own
//!   methods (`eq` is inherited through the premise).
//! * [`up_cast`] — `UpCast(A, B)`: the FAILURE-FREE cast into a supertype (the
//!   generalization of the elaborator's numeric-injection lattice
//!   `Nat ⊂ WNat ⊂ Int ⊂ Real`). `UpCast(T, T)` is BUILTIN (the identity, for
//!   every `T`, satisfied at resolution) and an explicit `UpCast(T, T)`
//!   instance is FORBIDDEN (an admission error, not an overlap). When the
//!   `Reduces` spine materializes as a concrete relation, `UpCast(A, B)`
//!   inherits `Reduces(A, B)` (cast = encode) — the owner's follow-up ruling;
//!   until then `UpCast` carries no `Reduces` premise.
//!
//! The numeric `UpCast` instances carry NO method bodies: the lukb elaborator
//! (F2) resolves this registry as the LICENSE for `=`/`!=`/comparisons, and
//! its existing injection constants (`nat2wnat`/`nat2int`/`to_real`, …) still
//! EXECUTE the cast — the instance set here mirrors that executor lattice
//! exactly, so gate and surgery agree by construction. Storing the injection
//! constants as `cast` method bodies (retiring the executor's own rank table)
//! is deferred until a consumer needs the method, not just the license.

use adsmt_core::{Kind, Term, Type, TyVar};
use std::sync::Arc;

use crate::instance::{Instance, Premise};
use crate::law::{Dict, Law, LawError};
use crate::numberlike::{apply2, close_forall};
use crate::relation::Relation;
use crate::resolve::InstanceDb;

// ── relation names ──────────────────────────────────────────────────────
pub const PARTIAL_EQ: &str = "PartialEq";
pub const EQ: &str = "Eq";
pub const UP_CAST: &str = "UpCast";

// ── method names ────────────────────────────────────────────────────────
/// Heterogeneous equality `A -> B -> Bool` (lives on `PartialEq`).
pub const M_EQ: &str = "eq";
/// The failure-free cast `A -> B` (lives on `UpCast`).
pub const M_CAST: &str = "cast";

fn tyvar(name: &str) -> Arc<TyVar> {
    Arc::new(TyVar { name: name.into(), kind: Kind::Type })
}

fn carrier_ty(sort: &str) -> Type {
    Type::const_(sort, Kind::Type)
}

fn fun2(a: Type, b: Type) -> Type {
    Type::fun(a, b).expect("kind")
}

/// `PartialEq(A, B)` — heterogeneous equality, `eq : A -> B -> Bool`.
pub fn partial_eq() -> Relation {
    let a = tyvar("A");
    let b = tyvar("B");
    let (at, bt) = (Type::Var(a.clone()), Type::Var(b.clone()));
    Relation::new(PARTIAL_EQ)
        .with_param(a)
        .with_param(b)
        .with_method(M_EQ, fun2(at, fun2(bt, Type::bool_())))
}

/// `Eq(T) : PartialEq(T, T)` — a conjunction marker; instances carry the
/// diagonal `PartialEq` premise and no own methods. Its LAWS are the
/// equivalence-relation + (classical) decidability obligations on the
/// inherited `eq` (resolved through the diagonal `PartialEq` premise, the
/// `Ord`/totality idiom) — a LAWFULLY admitted `Eq` instance (F3: the
/// per-`data` datatype derivation) has them discharged by the engine at the
/// concrete carrier; the builtin numeric/sort grants stay structural.
pub fn eq() -> Relation {
    Relation::new(EQ)
        .with_param(tyvar("T"))
        .with_law(Law::new("reflexivity", law_eq_reflexivity))
        .with_law(Law::new("symmetry", law_eq_symmetry))
        .with_law(Law::new("transitivity", law_eq_transitivity))
        .with_law(Law::new("decidability", law_eq_decidability))
}

/// `UpCast(A, B)` — the failure-free supertype cast, `cast : A -> B`.
pub fn up_cast() -> Relation {
    let a = tyvar("A");
    let b = tyvar("B");
    let (at, bt) = (Type::Var(a.clone()), Type::Var(b.clone()));
    Relation::new(UP_CAST)
        .with_param(a)
        .with_param(b)
        .with_method(M_CAST, fun2(at, bt))
}

/// The diagonal `PartialEq(T, T)` instance for a named sort. Carries the
/// `eq` method body — the kernel equality `=` at the carrier — so a LAWFUL
/// `Eq(T)` admission (whose laws reach `eq` through this premise) has a
/// concrete method to state its obligations over.
pub fn partial_eq_diag_instance(sort: &str) -> Instance {
    let c = carrier_ty(sort);
    let eq_body = Term::const_("=", fun2(c.clone(), fun2(c.clone(), Type::bool_())));
    Instance::new(PARTIAL_EQ, vec![c.clone(), c]).with_method(M_EQ, eq_body)
}

/// The `Eq(T)` instance for a named sort (premises the diagonal `PartialEq`).
pub fn eq_instance(sort: &str) -> Instance {
    let c = carrier_ty(sort);
    Instance::new(EQ, vec![c.clone()])
        .with_premise(Premise::new(PARTIAL_EQ, vec![c.clone(), c]))
}

/// A single-step numeric `UpCast(from, to)` instance. No `cast` method body:
/// the elaborator's injection constants execute the cast (module doc above).
pub fn up_cast_instance(from: &str, to: &str) -> Instance {
    Instance::new(UP_CAST, vec![carrier_ty(from), carrier_ty(to)])
}

// ── Eq laws (goal-members) ──────────────────────────────────────────────
//
// Stated over the inherited `eq` (the premise-aware `Dict` resolves it
// through the instance's diagonal `PartialEq` premise — the `Ord`/totality
// idiom). For the F3 datatype derivation `eq` is the kernel equality `=` at
// the carrier, so all four discharge in the engine as tiny EUF /
// propositional refutations; a carrier whose `eq` is NOT an equivalence (or
// not classically two-valued) is build-rejected.

fn law_eq_reflexivity(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let eq = d.require(M_EQ)?;
    let a = Term::var("a", c.clone());
    let body = apply2(&eq, a.clone(), a)?; // eq a a
    close_forall(&c, &["a"], body)
}

fn law_eq_symmetry(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let eq = d.require(M_EQ)?;
    let a = Term::var("a", c.clone());
    let b = Term::var("b", c.clone());
    let ab = apply2(&eq, a.clone(), b.clone())?;
    let ba = apply2(&eq, b, a)?;
    // eq a b ⟹ eq b a
    close_forall(&c, &["a", "b"], Term::mk_imp(ab, ba)?)
}

fn law_eq_transitivity(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let eq = d.require(M_EQ)?;
    let a = Term::var("a", c.clone());
    let b = Term::var("b", c.clone());
    let cc = Term::var("c", c.clone());
    let ab = apply2(&eq, a.clone(), b.clone())?;
    let bc = apply2(&eq, b, cc.clone())?;
    let ac = apply2(&eq, a, cc)?;
    // (eq a b ∧ eq b c) ⟹ eq a c
    let imp = Term::mk_imp(Term::mk_and(ab, bc)?, ac)?;
    close_forall(&c, &["a", "b", "c"], imp)
}

fn law_eq_decidability(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let eq = d.require(M_EQ)?;
    let a = Term::var("a", c.clone());
    let b = Term::var("b", c.clone());
    let ab = apply2(&eq, a, b)?;
    // eq a b ∨ ¬eq a b — the classical two-valuedness the spec names
    // ("distinctness + injectivity make eq decidable"): the datatype theory
    // decides which disjunct holds on ctor-shaped terms; the law pins that
    // `eq` admits no third value at the carrier.
    let disj = Term::mk_or(ab.clone(), Term::mk_not(ab)?)?;
    close_forall(&c, &["a", "b"], disj)
}

/// Declare the three relations.
pub fn declare_eq_ord_relations(db: &mut InstanceDb) {
    db.declare_relation(partial_eq());
    db.declare_relation(eq());
    db.declare_relation(up_cast());
}

/// The numeric builtin instances: diagonal `PartialEq`/`Eq` for the four
/// numeric carriers, and the `UpCast` lattice `Nat → WNat → Int → Real` with
/// its finite composition closure (`Nat→Int`, `Nat→Real`, `WNat→Real`).
/// `UpCast(T, T)` is NOT declared — it is the resolution-level builtin.
pub fn install_eq_ord_numeric(db: &mut InstanceDb) {
    const NUMERICS: [&str; 4] = ["Nat", "WNat", "Int", "Real"];
    for s in NUMERICS {
        db.declare_instance(partial_eq_diag_instance(s)).expect("PartialEq diag");
        db.declare_instance(eq_instance(s)).expect("Eq instance");
    }
    const STEPS: [(&str, &str); 6] = [
        ("Nat", "WNat"),
        ("WNat", "Int"),
        ("Int", "Real"),
        ("Nat", "Int"),
        ("Nat", "Real"),
        ("WNat", "Real"),
    ];
    for (from, to) in STEPS {
        db.declare_instance(up_cast_instance(from, to)).expect("UpCast step");
        // the heterogeneous equality along each lattice edge (the mirror is
        // synchronized by the registry), premising the UpCast that performs
        // the injection at elaboration.
        db.declare_instance(
            Instance::new(PARTIAL_EQ, vec![carrier_ty(from), carrier_ty(to)])
                .with_premise(Premise::new(UP_CAST, vec![carrier_ty(from), carrier_ty(to)])),
        )
        .expect("PartialEq edge");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolve::{ClassError, ClassGoal, ResolutionResult, Resolver};

    fn db() -> InstanceDb {
        let mut db = InstanceDb::new();
        declare_eq_ord_relations(&mut db);
        db
    }

    /// An explicit `UpCast(T, T)` instance is FORBIDDEN (builtin identity).
    #[test]
    fn explicit_identity_upcast_is_rejected() {
        let mut db = db();
        let c = carrier_ty("Int");
        let e = db.declare_instance(Instance::new(UP_CAST, vec![c.clone(), c]));
        assert_eq!(e, Err(ClassError::BuiltinIdentityUpCast));
    }

    /// `UpCast(τ, τ)` resolves as the BUILTIN identity (no stored instance).
    #[test]
    fn identity_upcast_resolves_builtin() {
        let db = db();
        let c = carrier_ty("Int");
        let r = Resolver::new(&db).resolve(&ClassGoal::new(UP_CAST, vec![c.clone(), c]));
        match r {
            ResolutionResult::Found(m) => assert!(m.sub_goals.is_empty(), "identity has no premises"),
            other => panic!("expected the builtin identity, got {other:?}"),
        }
    }

    /// Declaring `PartialEq(A, B)` with `A ≠ B` synchronizes the mirror
    /// `PartialEq(B, A)`; an explicit mirror afterwards is a coherence error.
    #[test]
    fn heterogeneous_partial_eq_synchronizes_the_mirror() {
        let mut db = db();
        let (a, b) = (carrier_ty("Nat"), carrier_ty("Int"));
        db.declare_instance(Instance::new(PARTIAL_EQ, vec![a.clone(), b.clone()]))
            .expect("declares");
        // the mirror resolves…
        let r = Resolver::new(&db).resolve(&ClassGoal::new(PARTIAL_EQ, vec![b.clone(), a.clone()]));
        match r {
            ResolutionResult::Found(m) => {
                assert_eq!(m.sub_goals.len(), 1, "mirror defers to the original");
                assert_eq!(m.sub_goals[0].relation, PARTIAL_EQ);
                assert_eq!(m.sub_goals[0].types, vec![a.clone(), b.clone()]);
            }
            other => panic!("expected the synchronized mirror, got {other:?}"),
        }
        // …and an explicit mirror is a duplicate.
        let e = db.declare_instance(Instance::new(PARTIAL_EQ, vec![b, a]));
        assert_eq!(e, Err(ClassError::CoherenceViolation));
    }

    /// A lawful `Eq` admission builds all four obligations (through the
    /// diagonal `PartialEq` premise's `eq` method) and gates on the prover:
    /// an all-accepting prover admits, an all-rejecting prover build-rejects
    /// with `LawUnproven` naming the first law.
    #[test]
    fn lawful_eq_gates_on_the_prover() {
        use crate::law::LawProver;
        struct Always;
        impl LawProver for Always {
            fn prove_valid(&self, _goal: &Term) -> bool {
                true
            }
        }
        struct Never;
        impl LawProver for Never {
            fn prove_valid(&self, _goal: &Term) -> bool {
                false
            }
        }
        let mut db = db();
        db.declare_instance(partial_eq_diag_instance("Color")).expect("diag PartialEq");
        let e = db.declare_instance_lawful(eq_instance("Color"), &Never);
        assert!(
            matches!(e, Err(ClassError::LawUnproven { ref law, .. }) if law == "reflexivity"),
            "rejecting prover build-rejects: {e:?}"
        );
        db.declare_instance_lawful(eq_instance("Color"), &Always).expect("lawful Eq admits");
        let r = Resolver::new(&db).resolve(&ClassGoal::new(EQ, vec![carrier_ty("Color")]));
        assert!(matches!(r, ResolutionResult::Found(_)), "Eq(Color) resolves after admission");
    }

    /// The numeric install: `Eq(Int)` resolves with its diagonal premise, and a
    /// composed lattice edge (`Nat → Real`) is present.
    #[test]
    fn numeric_install_resolves() {
        let mut db = db();
        install_eq_ord_numeric(&mut db);
        let r = Resolver::new(&db).resolve(&ClassGoal::new(EQ, vec![carrier_ty("Int")]));
        assert!(matches!(r, ResolutionResult::Found(_)), "Eq(Int)");
        let r = Resolver::new(&db)
            .resolve(&ClassGoal::new(UP_CAST, vec![carrier_ty("Nat"), carrier_ty("Real")]));
        assert!(matches!(r, ResolutionResult::Found(_)), "UpCast(Nat, Real)");
    }
}
