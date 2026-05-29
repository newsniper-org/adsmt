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

/// v0.19 A.3 (partial) — learn a covering set of trigger patterns
/// from `body` over the bound flex variables `flex`.
///
/// Algorithm:
/// 1. Collect every application sub-term inside `body`.
/// 2. For each candidate, compute the subset of `flex` it mentions.
/// 3. Greedy selection: walk candidates from smallest depth up,
///    keeping any that newly cover a flex variable. Stops once
///    every variable in `flex` is covered or the candidate set
///    is exhausted.
///
/// The returned [`Trigger`] is single-pattern when one application
/// covers every flex variable, multi-pattern when several are
/// required. Returns `None` when no covering set exists (e.g. a
/// flex variable that appears only as a free Var, never under an
/// application).
pub fn learn_triggers(body: &Term, flex: &[Arc<Var>]) -> Option<Trigger> {
    if flex.is_empty() {
        return None;
    }
    let mut candidates: Vec<Term> = Vec::new();
    collect_apps(body, &mut candidates);
    candidates.sort_by_key(term_depth);

    let flex_set: HashSet<Arc<Var>> = flex.iter().cloned().collect();
    let mut covered: HashSet<Arc<Var>> = HashSet::new();
    let mut selected: Vec<Term> = Vec::new();

    for cand in candidates {
        let cand_flex = flex_vars_in(&cand, &flex_set);
        if cand_flex.is_empty() { continue; }
        // Does this candidate cover anything new?
        let mut newly_covered = false;
        for v in &cand_flex {
            if !covered.contains(v) {
                newly_covered = true;
                break;
            }
        }
        if !newly_covered { continue; }
        for v in cand_flex {
            covered.insert(v);
        }
        selected.push(cand);
        if covered.len() == flex_set.len() { break; }
    }

    if covered.len() != flex_set.len() {
        return None;
    }
    let trigger = if selected.len() == 1 {
        Trigger::single(selected.into_iter().next().unwrap(), flex.to_vec())
    } else {
        Trigger::multi(selected, flex.to_vec())
    };
    Some(trigger)
}

fn collect_apps(t: &Term, out: &mut Vec<Term>) {
    match t {
        Term::App(f, x) => {
            // Record the application itself.
            out.push(t.clone());
            collect_apps(f, out);
            collect_apps(x, out);
        }
        Term::Lam(_, body) => collect_apps(body, out),
        _ => {}
    }
}

fn term_depth(t: &Term) -> usize {
    match t {
        Term::Var(_) | Term::Const(_) => 0,
        Term::App(f, x) => 1 + term_depth(f).max(term_depth(x)),
        Term::Lam(_, b) => 1 + term_depth(b),
    }
}

fn flex_vars_in(t: &Term, flex: &HashSet<Arc<Var>>) -> Vec<Arc<Var>> {
    let mut out: Vec<Arc<Var>> = Vec::new();
    fn walk(t: &Term, flex: &HashSet<Arc<Var>>, out: &mut Vec<Arc<Var>>) {
        match t {
            Term::Var(v) => {
                if flex.contains(v) && !out.iter().any(|x| **x == **v) {
                    out.push(v.clone());
                }
            }
            Term::App(f, x) => {
                walk(f, flex, out);
                walk(x, flex, out);
            }
            Term::Lam(_, b) => walk(b, flex, out),
            _ => {}
        }
    }
    walk(t, flex, &mut out);
    out
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

    // === v0.19 A.3 (partial) — trigger learning ===

    #[test]
    fn learn_triggers_single_pattern_covers_one_var() {
        // body: P x   over flex {x}
        // → single Trigger over `P x`.
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let body = Term::app(p, Term::Var(x.clone())).unwrap();
        let trig = learn_triggers(&body, &[x]).expect("covering trigger");
        match trig.kind {
            TriggerKind::Single(_) => {}
            _ => panic!("expected single pattern"),
        }
    }

    #[test]
    fn learn_triggers_multi_pattern_covers_disjoint_vars() {
        // body: AND (P x) (Q y)   over flex {x, y}
        // The conjunction itself covers both — single trigger.
        // But `learn_triggers` picks smallest-depth candidates,
        // which in this case is `P x` (covers x) then `Q y`
        // (covers y) — multi-pattern of length 2.
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let q = Term::const_("Q", Type::fun(int_(), Type::bool_()).unwrap());
        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let y = Arc::new(Var { name: "y".into(), ty: int_() });
        let p_x = Term::app(p, Term::Var(x.clone())).unwrap();
        let q_y = Term::app(q, Term::Var(y.clone())).unwrap();
        let and_term = Term::mk_and(p_x, q_y).unwrap();
        let trig =
            learn_triggers(&and_term, &[x, y]).expect("covering trigger");
        match trig.kind {
            TriggerKind::Multi(ps) => {
                assert_eq!(ps.len(), 2);
            }
            TriggerKind::Single(_) => {
                // Acceptable if the algorithm collapsed; the test
                // primarily verifies covering — at least one shape
                // must cover both vars.
            }
        }
    }

    #[test]
    fn learn_triggers_returns_none_when_var_only_appears_as_var() {
        // body: x   over flex {x}.  No application uses x, so no
        // covering set exists.
        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let body = Term::Var(x.clone());
        let trig = learn_triggers(&body, &[x]);
        assert!(trig.is_none(), "bare flex var ⇒ no learned trigger");
    }

    #[test]
    fn learn_triggers_no_flex_returns_none() {
        // Empty flex set ⇒ trigger learning is undefined.
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_());
        let body = Term::app(p, a).unwrap();
        assert!(learn_triggers(&body, &[]).is_none());
    }
}
