//! Trigger patterns for E-matching.
//!
//! v0.1 supports single and multi triggers, and detects whether a
//! pattern conforms to the Miller restriction (every flex-head
//! application uses *distinct bound variables* as arguments). The
//! engine defaults to Miller; non-Miller patterns require the
//! `:trigger!` escape hatch (per Q12 in sec 18).

use std::collections::HashSet;
use std::sync::Arc;

use adsmt_core::{Term, Var};

#[derive(Clone, Debug)]
pub enum TriggerKind {
    Single(Term),
    Multi(Vec<Term>),
}

#[derive(Clone, Debug)]
pub struct Trigger {
    pub kind: TriggerKind,
    /// Bound variables this trigger may instantiate.
    pub bound: Vec<Arc<Var>>,
}

impl Trigger {
    pub fn single(pattern: Term, bound: Vec<Arc<Var>>) -> Self {
        Self { kind: TriggerKind::Single(pattern), bound }
    }

    pub fn multi(patterns: Vec<Term>, bound: Vec<Arc<Var>>) -> Self {
        Self { kind: TriggerKind::Multi(patterns), bound }
    }

    /// Is every pattern in this trigger a Miller pattern with respect
    /// to its bound variables?
    pub fn is_miller(&self) -> bool {
        let bound_set: HashSet<Arc<Var>> = self.bound.iter().cloned().collect();
        match &self.kind {
            TriggerKind::Single(t) => miller_check(t, &bound_set),
            TriggerKind::Multi(ts) => ts.iter().all(|t| miller_check(t, &bound_set)),
        }
    }
}

fn miller_check(term: &Term, flex: &HashSet<Arc<Var>>) -> bool {
    let (head, args) = uncurry(term);
    if let Term::Var(v) = &head
        && flex.contains(v) {
            // Flex head: arguments must be distinct rigid bound variables,
            // i.e. not other flex variables.
            let mut seen: Vec<Arc<Var>> = Vec::new();
            for a in &args {
                match a {
                    Term::Var(av) if !flex.contains(av) => {
                        if seen.iter().any(|x| **x == **av) {
                            return false;
                        }
                        seen.push(av.clone());
                    }
                    _ => return false,
                }
            }
            return true;
        }
    // Rigid head: recurse into arguments and into the head itself.
    if let Term::Lam(_, body) = &head
        && !miller_check(body, flex) {
            return false;
        }
    args.iter().all(|a| miller_check(a, flex))
}

fn uncurry(t: &Term) -> (Term, Vec<Term>) {
    let mut args: Vec<Term> = Vec::new();
    let mut cur = t.clone();
    while let Term::App(f, a) = &cur {
        args.insert(0, (**a).clone());
        let next = (**f).clone();
        cur = next;
    }
    (cur, args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn rigid_head_with_bound_arg_is_miller() {
        // pattern: P x (where P is rigid, x is bound)
        let x_var = Arc::new(Var { name: "x".into(), ty: int_() });
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let pattern = Term::app(p, Term::Var(x_var.clone())).unwrap();
        let trig = Trigger::single(pattern, vec![]);
        assert!(trig.is_miller());
    }

    #[test]
    fn flex_head_distinct_bound_args_is_miller() {
        // pattern: F x y    where F is bound (flex), x and y are distinct outer-bound vars
        let f_ty = Type::fun(int_(), Type::fun(int_(), Type::bool_()).unwrap()).unwrap();
        let f_var = Arc::new(Var { name: "F".into(), ty: f_ty });
        let x_var = Arc::new(Var { name: "x".into(), ty: int_() });
        let y_var = Arc::new(Var { name: "y".into(), ty: int_() });
        let f_x = Term::app(Term::Var(f_var.clone()), Term::Var(x_var)).unwrap();
        let f_x_y = Term::app(f_x, Term::Var(y_var)).unwrap();
        let trig = Trigger::single(f_x_y, vec![f_var]);
        assert!(trig.is_miller());
    }

    #[test]
    fn flex_head_repeated_arg_violates_miller() {
        // pattern: F x x — repeated bound var
        let f_ty = Type::fun(int_(), Type::fun(int_(), Type::bool_()).unwrap()).unwrap();
        let f_var = Arc::new(Var { name: "F".into(), ty: f_ty });
        let x_var = Arc::new(Var { name: "x".into(), ty: int_() });
        let f_x = Term::app(Term::Var(f_var.clone()), Term::Var(x_var.clone())).unwrap();
        let f_x_x = Term::app(f_x, Term::Var(x_var)).unwrap();
        let trig = Trigger::single(f_x_x, vec![f_var]);
        assert!(!trig.is_miller());
    }

    #[test]
    fn flex_head_with_non_var_arg_violates_miller() {
        // pattern: F (c) where c is a constant
        let f_ty = Type::fun(int_(), Type::bool_()).unwrap();
        let f_var = Arc::new(Var { name: "F".into(), ty: f_ty });
        let c = Term::const_("c", int_());
        let f_c = Term::app(Term::Var(f_var.clone()), c).unwrap();
        let trig = Trigger::single(f_c, vec![f_var]);
        assert!(!trig.is_miller());
    }
}
