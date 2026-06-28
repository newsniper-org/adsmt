//! An engine-backed [`LawProver`] for the type-class layer's proof-gated
//! instance admission.
//!
//! The `adsmt-class` layer defines goal-members (laws) on a type relation and a
//! gate ([`adsmt_class::InstanceDb::declare_instance_lawful`]) that admits an
//! instance only if every law is *proven*. It injects the proof obligation
//! through the [`LawProver`] trait so the class layer need not depend on the
//! solver. [`EngineLawProver`] supplies the real proof: it discharges an
//! obligation with adsmt's own engine — realising the user's
//! "어떤 식으로든 반드시 전부 성공적으로 증명한 인스턴스들만을 유효한 instance".
//!
//! A law obligation is a closed prenex-universal proposition `∀x̄. φ` with a
//! quantifier-free matrix (e.g. order totality `∀a b. le a b ∨ le b a`).
//! Validity is checked the standard way — `∀x̄. φ` is valid iff `¬φ` is
//! unsatisfiable after the universals are replaced by fresh Skolem constants —
//! which turns the check into the engine's strongest path: a ground refutation.
//!
//! **Soundness.** `prove_valid` returns `true` only on a definite `Unsat`; a
//! `Sat`/`Unknown`/anything-else maps to `false`. Per the [`LawProver`]
//! contract a `false` merely *rejects* an instance (conservative), so an engine
//! incompleteness can never admit an unlawful instance — it can only over-reject
//! a lawful one.
//!
//! **Native reach.** This prover uses the in-process native engine. Its
//! `LinArith` discharges the full integer/real order-law set over `Int.le` —
//! reflexivity, antisymmetry, transitivity, totality — so the proof-gated gate
//! admits `PartialOrd(Int)`/`Ord(Int)`. (Antisymmetry and transitivity became
//! native-provable once the two-var false-sat fixes landed: direction-symmetric
//! dominance, `≥`/`>`→`≤`/`<` normalization so the FM closure chains every
//! direction, and the var-var-disequality pinned-equality rule for the
//! arith→EUF interface.) Two reaches remain native-`Unknown` → conservative
//! `false` (reject, never an unsound admit): richer linear-arith goals (where
//! the production build delegates to OxiZ), and order laws over the refinement
//! carriers `Nat`/`WNat` — their `le` routes through `nat2int`/`wnat2int`, and
//! LinArith keys arith variables on bare `Var`s, not on a function application.
//! An OxiZ-delegating `LawProver` (or LinArith treating an injection
//! application as an arith atom) would close those — a possible follow-up, not
//! needed for the `Int` order laws.

use std::sync::Arc;

use adsmt_class::LawProver;
use adsmt_core::{Term, TermInner, Var};
use indexmap::IndexMap;

use crate::{SatResult, Solver};

/// Discharges type-relation law obligations with the adsmt engine.
#[derive(Debug, Default, Clone, Copy)]
pub struct EngineLawProver;

impl EngineLawProver {
    pub fn new() -> Self {
        Self
    }
}

impl LawProver for EngineLawProver {
    fn prove_valid(&self, goal: &Term) -> bool {
        // `∀x̄. φ` is valid iff `¬φ[x̄ ↦ fresh consts]` is unsatisfiable.
        // The negation is asserted as a positive term (`not` *inside* the
        // formula) rather than via `assert_negated`, so the engine's CNF
        // pre-pass registers the inner comparison as a theory atom — a
        // literal-level polarity flip leaves it an uninterpreted boolean.
        let matrix = lower_arith_ops(&skolemize_prenex_universals(goal));
        let negation = match Term::mk_not(matrix) {
            Ok(t) => t,
            Err(_) => return false, // matrix not Bool — cannot prove; reject conservatively
        };
        let mut solver = Solver::new();
        solver.assert(negation);
        matches!(solver.check_sat(), SatResult::Unsat { .. })
    }
}

/// Rewrite the kernel/IR arithmetic operator names the type-class dictionaries
/// carry (`Int.le`, `Int.add`, …, mirrored from `adsmt_ir::theory`) into the
/// SMT-LIB names the engine's arith theory interprets (`<=`, `+`, …) — the same
/// mapping `adsmt-ir-lower` applies on the real solve path. Without this the
/// engine treats `Int.le` as an uninterpreted EUF predicate and cannot discharge
/// an order law. Constant *types* are preserved; only the name is rewritten.
fn lower_arith_ops(t: &Term) -> Term {
    match t.kind() {
        TermInner::Const(c) => match engine_op_name(&c.name) {
            Some(name) => Term::const_(name, c.ty.clone()),
            None => t.clone(),
        },
        TermInner::Var(_) => t.clone(),
        TermInner::App(f, x) => Term::App(lower_arith_ops(f), lower_arith_ops(x)),
        TermInner::Lam(v, body) => Term::Lam(v.clone(), lower_arith_ops(body)),
    }
}

/// The `adsmt_ir::theory` binary-operator → SMT-LIB-name map, mirroring
/// `adsmt-ir-lower::lower`'s `try_arith`. (Int and Real share the symbol; the
/// operand sorts disambiguate.) Unary `Int.neg`/`abs` are not needed by the
/// order/positivity laws and are left for the consumer that introduces them.
fn engine_op_name(kernel: &str) -> Option<&'static str> {
    Some(match kernel {
        "Int.add" | "Real.add" => "+",
        "Int.sub" | "Real.sub" => "-",
        "Int.mul" | "Real.mul" => "*",
        "Int.div" => "div",
        "Int.mod" => "mod",
        "Real.div" => "/",
        "Int.lt" | "Real.lt" => "<",
        "Int.le" | "Real.le" => "<=",
        "Int.gt" | "Real.gt" => ">",
        "Int.ge" | "Real.ge" => ">=",
        _ => return None,
    })
}

/// Strip the leading universal quantifiers of a prenex obligation, replacing
/// each bound variable with a fresh Skolem constant of the same sort, and return
/// the resulting matrix. A non-prenex / non-universal goal (no leading `∀`) is
/// returned unchanged — `assert_negated` then handles whatever remains, and a
/// resulting `Unknown`/`Sat` simply yields a conservative `false`.
fn skolemize_prenex_universals(goal: &Term) -> Term {
    let mut t = goal.clone();
    let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
    let mut n = 0usize;
    while let Some((v, body)) = t.dest_forall() {
        // A Skolem for a top-level `∀` is a fresh free *variable* (not a
        // `const`): the engine's arith theory keys on `TermInner::Var` (the
        // parser likewise represents `(declare-const a Int)` as a `Var`), so a
        // `const`-shaped Skolem would be ignored by LinArith and the atom would
        // come back uninterpreted.
        let sk = Term::var(&format!("!classlaw.sk.{}.{n}", v.name), v.ty.clone());
        n += 1;
        sigma.insert(Arc::new(v), sk);
        t = body;
    }
    // Substitute all collected Skolem constants into the innermost matrix at
    // once (binders are distinct, images are closed → no capture). If the
    // (type-checked) substitution somehow fails, fall back to the unsubstituted
    // matrix: still sound, since a stray free variable only weakens the proof.
    t.subst(&sigma).unwrap_or(t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_class::{ord, partial_ord, ClassError, Dict, InstanceDb, Relation};
    use adsmt_core::{Kind, Type};

    /// A standalone Int dictionary exposing `le ↦ Int.le`, for building an
    /// order obligation and handing it straight to the prover.
    struct IntLeDict(Type, Term);
    impl Dict for IntLeDict {
        fn carriers(&self) -> &[Type] {
            std::slice::from_ref(&self.0)
        }
        fn method(&self, n: &str) -> Option<Term> {
            (n == "le").then(|| self.1.clone())
        }
    }
    fn int_le_dict() -> IntLeDict {
        let int = Type::const_("Int", Kind::Type);
        let le = Term::const_(
            "Int.le",
            Type::fun(int.clone(), Type::fun(int.clone(), Type::bool_()).unwrap()).unwrap(),
        );
        IntLeDict(int, le)
    }
    fn law(r: &Relation, name: &str, d: &dyn Dict) -> Term {
        let l = r.laws.iter().find(|l| l.name == name).expect("law present");
        (l.build)(d).expect("obligation builds")
    }

    #[test]
    fn engine_proves_the_full_order_law_set() {
        // adsmt's own engine discharges every PartialOrd/Ord law over Int.le:
        // reflexivity, antisymmetry, transitivity, totality. (Antisymmetry and
        // transitivity became native-provable once the two-var LinArith
        // false-sat fixes landed — direction-symmetric dominance + ≥/>→≤/<
        // normalization + the var-var-disequality pinned-equality rule.)
        let d = int_le_dict();
        let prover = EngineLawProver;
        for (rel, name) in [
            (partial_ord(), "reflexivity"),
            (partial_ord(), "antisymmetry"),
            (partial_ord(), "transitivity"),
            (ord(), "totality"),
        ] {
            assert!(prover.prove_valid(&law(&rel, name, &d)), "{}::{name}", rel.name);
        }
    }

    #[test]
    fn engine_lawfully_admits_the_int_order_instances() {
        // The original goal, realised for the `Int` carrier: adsmt's own solver
        // proves every order law over `Int.le`, so the proof-gated gate admits
        // `PartialOrd(Int)` (reflexivity/antisymmetry/transitivity) and
        // `Ord(Int)` (totality, resolving `le` through the PartialOrd premise).
        //
        // The refinement carriers `Nat`/`WNat` route `le` through `nat2int`/
        // `wnat2int`, so their order obligations compare `nat2int(x)` terms;
        // native LinArith keys arith variables on bare `Var`s, not on a
        // function application, so those stay native-`Unknown` → conservative
        // reject. Admitting them needs either an OxiZ-delegating prover or
        // LinArith treating an injection application as an arith atom — tracked,
        // not required for the order laws over `Int`.
        use adsmt_class::{Instance, Premise};
        use adsmt_core::{Kind, Type};
        let int = Type::const_("Int", Kind::Type);
        let le = Term::const_(
            "Int.le",
            Type::fun(int.clone(), Type::fun(int.clone(), Type::bool_()).unwrap()).unwrap(),
        );
        let mut db = InstanceDb::new();
        db.declare_relation(partial_ord());
        db.declare_relation(ord());
        db.declare_instance_lawful(
            Instance::new("PartialOrd", vec![int.clone()]).with_method("le", le),
            &EngineLawProver,
        )
        .expect("engine proves PartialOrd(Int)'s reflexivity/antisymmetry/transitivity");
        db.declare_instance_lawful(
            Instance::new("Ord", vec![int.clone()]).with_premise(Premise::new("PartialOrd", vec![int])),
            &EngineLawProver,
        )
        .expect("engine proves Ord(Int)'s totality via the PartialOrd premise");
    }

    fn real_le_dict() -> IntLeDict {
        let real = Type::const_("Real", Kind::Type);
        let le = Term::const_(
            "Real.le",
            Type::fun(real.clone(), Type::fun(real.clone(), Type::bool_()).unwrap()).unwrap(),
        );
        IntLeDict(real, le)
    }

    #[test]
    fn engine_proves_the_full_order_law_set_over_real() {
        // The field-side sibling of `engine_proves_the_full_order_law_set`: adsmt's
        // own engine discharges every PartialOrd/Ord law over `Real.le` too
        // (`Real.le → "<="`, an LRA dense total order — the same LinArith path,
        // over the rationals instead of the integers).
        let d = real_le_dict();
        let prover = EngineLawProver;
        for (rel, name) in [
            (partial_ord(), "reflexivity"),
            (partial_ord(), "antisymmetry"),
            (partial_ord(), "transitivity"),
            (ord(), "totality"),
        ] {
            assert!(prover.prove_valid(&law(&rel, name, &d)), "Real {}::{name}", rel.name);
        }
    }

    #[test]
    fn engine_lawfully_admits_the_real_order_instances() {
        // `RealLike`'s order is proof-gated exactly like the integers': the engine
        // proves `PartialOrd(Real)`'s reflexivity/antisymmetry/transitivity and
        // `Ord(Real)`'s totality over `Real.le`, then `RealLike(Real)` (no own
        // laws) is admitted once its `PartialOrd(Real)` premise is in place.
        use adsmt_class::{numberlike, Instance, Premise};
        let real = Type::const_("Real", Kind::Type);
        let le = Term::const_(
            "Real.le",
            Type::fun(real.clone(), Type::fun(real.clone(), Type::bool_()).unwrap()).unwrap(),
        );
        let mut db = InstanceDb::new();
        db.declare_relation(partial_ord());
        db.declare_relation(ord());
        db.declare_relation(numberlike::real_like());
        db.declare_instance_lawful(
            Instance::new("PartialOrd", vec![real.clone()]).with_method("le", le),
            &EngineLawProver,
        )
        .expect("engine proves PartialOrd(Real)'s order laws");
        db.declare_instance_lawful(
            Instance::new("Ord", vec![real.clone()])
                .with_premise(Premise::new("PartialOrd", vec![real.clone()])),
            &EngineLawProver,
        )
        .expect("engine proves Ord(Real)'s totality");
        db.declare_instance_lawful(
            Instance::new("RealLike", vec![real.clone()])
                .with_premise(Premise::new("PartialOrd", vec![real])),
            &EngineLawProver,
        )
        .expect("RealLike(Real) admitted (no own laws)");
    }

    #[test]
    fn engine_rejects_a_false_order_law() {
        // A carrier whose `le` is a strict order is NOT reflexive, so the
        // obligation `∀a. lt a a` is invalid and must be rejected (build-reject).
        use adsmt_class::{Instance, Law, LawError};

        fn bad_reflexivity(d: &dyn Dict) -> Result<Term, LawError> {
            let c = d.carrier0()?;
            let lt = d.require("lt")?;
            let a = Term::var("a", c.clone());
            let body = Term::app(Term::app(lt, a.clone())?, a)?; // ∀a. Int.lt a a
            let v = Var { name: "a".into(), ty: c };
            Ok(Term::mk_forall(v, body)?)
        }

        let mut db = InstanceDb::new();
        let i = Arc::new(adsmt_core::TyVar { name: "I".into(), kind: Kind::Type });
        let it = Type::Var(i.clone());
        db.declare_relation(
            Relation::new("StrictOrd")
                .with_param(i)
                .with_method("lt", Type::fun(it.clone(), Type::fun(it, Type::bool_()).unwrap()).unwrap())
                .with_law(Law::new("reflexivity", bad_reflexivity)),
        );
        let int = Type::const_("Int", Kind::Type);
        let lt = Term::const_(
            "Int.lt",
            Type::fun(int.clone(), Type::fun(int.clone(), Type::bool_()).unwrap()).unwrap(),
        );
        let inst = Instance::new("StrictOrd", vec![int]).with_method("lt", lt);
        let err = db.declare_instance_lawful(inst, &EngineLawProver).unwrap_err();
        assert!(matches!(err, ClassError::LawUnproven { .. }), "irreflexive lt rejected: {err:?}");
    }
}
