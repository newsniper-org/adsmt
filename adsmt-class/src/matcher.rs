//! First-order type matching for instance resolution.
//!
//! Given a pattern (instance head with free type variables) and a
//! target (the goal's concrete types), produce a substitution σ such
//! that `pattern[σ] = target`. Kind-respecting; HKT-aware up to the
//! FOU restriction agreed in sec 12 — no higher-order matching.

use std::sync::Arc;

use adsmt_core::{TyVar, Type};
use indexmap::IndexMap;

/// One-sided type matching. Mutates `sigma` with new bindings.
///
/// Returns `true` iff `pattern` matches `target` consistently with the
/// current `sigma`.
pub fn match_type(
    pattern: &Type,
    target: &Type,
    sigma: &mut IndexMap<Arc<TyVar>, Type>,
) -> bool {
    match (pattern, target) {
        (Type::Var(v), t) => {
            if v.kind != t.kind_of() {
                return false;
            }
            if let Some(bound) = sigma.get(v) {
                bound == t
            } else {
                sigma.insert(v.clone(), t.clone());
                true
            }
        }
        (Type::Const(c1), Type::Const(c2)) => **c1 == **c2,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            match_type(f1, f2, sigma) && match_type(a1, a2, sigma)
        }
        _ => false,
    }
}

/// Match a vector of patterns against a vector of targets.
pub fn match_types(
    patterns: &[Type],
    targets: &[Type],
    sigma: &mut IndexMap<Arc<TyVar>, Type>,
) -> bool {
    if patterns.len() != targets.len() {
        return false;
    }
    patterns
        .iter()
        .zip(targets.iter())
        .all(|(p, t)| match_type(p, t, sigma))
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }
    fn list() -> Type { Type::const_("List", Kind::first_order(1)) }

    #[test]
    fn matches_concrete_against_variable() {
        let alpha = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        let pat = Type::Var(alpha.clone());
        let mut sigma = IndexMap::new();
        assert!(match_type(&pat, &int_(), &mut sigma));
        assert_eq!(sigma.get(&alpha).cloned(), Some(int_()));
    }

    #[test]
    fn rejects_kind_mismatch() {
        let f_var = Arc::new(TyVar { name: "F".into(), kind: Kind::first_order(1) });
        let pat = Type::Var(f_var);
        let mut sigma = IndexMap::new();
        assert!(!match_type(&pat, &int_(), &mut sigma)); // F : *->* vs Int : *
    }

    #[test]
    fn matches_through_application() {
        // pattern: List α   target: List Int
        let alpha = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        let pat = Type::app(list(), Type::Var(alpha.clone())).unwrap();
        let target = Type::app(list(), int_()).unwrap();
        let mut sigma = IndexMap::new();
        assert!(match_type(&pat, &target, &mut sigma));
        assert_eq!(sigma.get(&alpha).cloned(), Some(int_()));
    }

    #[test]
    fn rejects_constant_mismatch() {
        let int_to_int = Type::fun(int_(), int_()).unwrap();
        let mut sigma = IndexMap::new();
        assert!(!match_type(&int_(), &int_to_int, &mut sigma));
    }

    #[test]
    fn consistent_repeated_var() {
        // pattern: (List α, α)   target: (List Int, Int) — consistent
        let alpha = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        let pats = vec![
            Type::app(list(), Type::Var(alpha.clone())).unwrap(),
            Type::Var(alpha.clone()),
        ];
        let targets = vec![Type::app(list(), int_()).unwrap(), int_()];
        let mut sigma = IndexMap::new();
        assert!(match_types(&pats, &targets, &mut sigma));
        assert_eq!(sigma.get(&alpha).cloned(), Some(int_()));
    }

    #[test]
    fn rejects_inconsistent_repeated_var() {
        // pattern: (α, α)   target: (Int, List Int) — α can't be both
        let alpha = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        let pats = vec![Type::Var(alpha.clone()), Type::Var(alpha)];
        let targets = vec![int_(), Type::app(list(), int_()).unwrap()];
        let mut sigma = IndexMap::new();
        assert!(!match_types(&pats, &targets, &mut sigma));
    }
}
