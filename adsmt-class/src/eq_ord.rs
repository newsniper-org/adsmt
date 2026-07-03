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
//! Method BODIES for the numeric `UpCast` instances (the injection constants)
//! are wired in F2 together with the elaborator reroute — F1 declares the
//! structure and the gates.

use adsmt_core::{Kind, Type, TyVar};
use std::sync::Arc;

use crate::instance::{Instance, Premise};
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
/// diagonal `PartialEq` premise and no own methods.
pub fn eq() -> Relation {
    Relation::new(EQ).with_param(tyvar("T"))
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

/// The diagonal `PartialEq(T, T)` instance for a named sort.
pub fn partial_eq_diag_instance(sort: &str) -> Instance {
    let c = carrier_ty(sort);
    Instance::new(PARTIAL_EQ, vec![c.clone(), c])
}

/// The `Eq(T)` instance for a named sort (premises the diagonal `PartialEq`).
pub fn eq_instance(sort: &str) -> Instance {
    let c = carrier_ty(sort);
    Instance::new(EQ, vec![c.clone()])
        .with_premise(Premise::new(PARTIAL_EQ, vec![c.clone(), c]))
}

/// A single-step numeric `UpCast(from, to)` instance. The cast method body
/// (the injection constant) is wired in F2 with the elaborator reroute.
pub fn up_cast_instance(from: &str, to: &str) -> Instance {
    Instance::new(UP_CAST, vec![carrier_ty(from), carrier_ty(to)])
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
