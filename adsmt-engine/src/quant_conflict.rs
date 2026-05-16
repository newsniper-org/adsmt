//! Conflict-based quantifier instantiation (Tier 2, v0.7).
//!
//! After Tier 1 (Miller-pattern E-matching) makes no progress on a
//! forall, Tier 2 tries to find an instantiation that *directly*
//! contradicts an existing ground assertion. The strategy:
//!
//! 1. Collect negative ground assertions matching the shape of
//!    `body`. Their atoms become "conflict templates".
//! 2. For each template, unify `body` against the template's atom
//!    (treating the bound variable as flex).
//! 3. If unification succeeds, the corresponding instantiation
//!    creates a positive/negative contradiction at the ground level.
//!
//! v0.7 alpha handles the simple case `∀x. P x` with a ground
//! `¬(P a)` — unification yields `x ↦ a`, the instantiation `P a`
//! directly contradicts `¬(P a)`. More elaborate conflict search
//! (multi-step unification, theory-driven goal generation) lands in
//! v0.9.

use std::sync::Arc;

use adsmt_core::{Term, Var};
use indexmap::IndexMap;

/// Find conflict-driving instantiations of `∀var. body` against
/// negatively asserted atoms in `ground`.
///
/// Returns the instantiated bodies that should be re-asserted as
/// ground positive literals; each is guaranteed to contradict at
/// least one entry in `ground`.
pub fn conflict_instantiate(
    var: &Var,
    body: &Term,
    ground: &[(Term, bool)],
) -> Vec<Term> {
    let v_arc = Arc::new(var.clone());
    let mut out = Vec::new();
    for (atom, polarity) in ground {
        if *polarity { continue; }  // we want NEGATIVE ground atoms to attack
        let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
        if extend_match(body, atom, &v_arc, &mut sigma) {
            // Build the instantiated body using the discovered binding.
            if let Ok(instantiated) = body.subst(&sigma)
                && !out.iter().any(|t: &Term| t.alpha_eq(&instantiated)) {
                    out.push(instantiated);
                }
        }
    }
    out
}

/// One-sided pattern match: try to unify `pattern` against `target`
/// using only the single flex variable `flex`.
fn extend_match(
    pattern: &Term,
    target: &Term,
    flex: &Arc<Var>,
    sigma: &mut IndexMap<Arc<Var>, Term>,
) -> bool {
    match (pattern, target) {
        (Term::Var(v), t) if **v == **flex => {
            if v.ty != t.type_of() {
                return false;
            }
            if let Some(prev) = sigma.get(v) {
                return prev.alpha_eq(t);
            }
            sigma.insert(v.clone(), t.clone());
            true
        }
        (Term::Var(a), Term::Var(b)) => **a == **b,
        (Term::Const(a), Term::Const(b)) => **a == **b,
        (Term::App(f1, x1), Term::App(f2, x2)) => {
            extend_match(f1, f2, flex, sigma) && extend_match(x1, x2, flex, sigma)
        }
        (Term::Lam(v1, b1), Term::Lam(v2, b2)) => {
            v1.ty == v2.ty && extend_match(b1, b2, flex, sigma)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    #[test]
    fn finds_conflict_witness_for_simple_forall() {
        // ∀x:Int. P x   vs   ground: ¬(P a)
        let int_ = Type::const_("Int", adsmt_core::Kind::Type);
        let p = Term::const_("P", Type::fun(int_.clone(), Type::bool_()).unwrap());
        let a = Term::var("a", int_.clone());
        let x_var = Var { name: "x".into(), ty: int_ };
        let body = Term::app(p.clone(), Term::Var(Arc::new(x_var.clone()))).unwrap();
        let ground = vec![(Term::app(p, a.clone()).unwrap(), false)];
        let instances = conflict_instantiate(&x_var, &body, &ground);
        assert_eq!(instances.len(), 1);
        // The instantiation should be `P a`.
        assert!(instances[0].to_string().contains("a"));
    }

    #[test]
    fn ignores_positive_ground_atoms() {
        // Only negative ground atoms drive conflicts.
        let int_ = Type::const_("Int", adsmt_core::Kind::Type);
        let p = Term::const_("P", Type::fun(int_.clone(), Type::bool_()).unwrap());
        let a = Term::var("a", int_.clone());
        let x_var = Var { name: "x".into(), ty: int_ };
        let body = Term::app(p.clone(), Term::Var(Arc::new(x_var.clone()))).unwrap();
        let ground = vec![(Term::app(p, a).unwrap(), true)];
        let instances = conflict_instantiate(&x_var, &body, &ground);
        assert!(instances.is_empty());
    }
}
