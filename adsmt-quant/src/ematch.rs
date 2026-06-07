//! E-matching skeleton.
//!
//! Provides [`TermUniverse`] and a one-shot pattern matcher that,
//! given a [`Trigger`], returns instantiations grounding the flex
//! variables against terms drawn from the universe. The current
//! implementation is intentionally simple: it scans the universe
//! per-trigger without congruence closure or incremental indexing.
//! That heavier machinery is a deliberate v0.17+ candidate — for
//! the goals adsmt drives today (quantifier tier-1 / tier-2), the
//! linear scan is sufficient.

use std::sync::Arc;

use adsmt_core::{Term, TermInner, Var};
use indexmap::{IndexMap, IndexSet};

use crate::trigger::{Trigger, TriggerKind};

/// E-matching term universe.
///
/// rc.24 (e'''.1) — the backing store is an `IndexSet<Term>`,
/// not a `Vec<Term>`.  Pre-rc.24 `insert` ran a
/// `self.terms.iter().any(|x| x.alpha_eq(&t))` linear scan
/// for dedup, which the verus-fork rc.23 retry flamegraph
/// localised as **97.50 % of cycles** on verus_smoke: every
/// `gather_subterms` walk calls `insert` ~N times against a
/// universe of size ~N, so the build is O(N²·alpha_eq_depth).
/// `IndexSet<Term>::insert` is O(1) (rc.10 hash-cons makes
/// `Term::Hash` pointer-hash and `Term::Eq` `Arc::ptr_eq`),
/// collapsing the build to O(N).
///
/// `IndexSet` (not `std::collections::HashSet`) because the
/// universe is iterated (`iter()` feeds the matcher),
/// `extend_with_equalities` snapshots it positionally, and
/// downstream match order should stay reproducible run-to-run.
#[derive(Default, Clone, Debug)]
pub struct TermUniverse {
    terms: IndexSet<Term>,
}

impl TermUniverse {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, t: Term) {
        // `IndexSet::insert` dedups in O(1) on the hash-cons
        // handles — no pre-`iter().any(alpha_eq)` scan needed.
        self.terms.insert(t);
    }

    /// O(1) membership probe via the rc.10 hash-cons handles.
    /// Replaces the `universe.iter().any(|t| q.alpha_eq(t))`
    /// linear scans in the engine-side quantifier loop.
    pub fn contains(&self, t: &Term) -> bool { self.terms.contains(t) }

    pub fn iter(&self) -> impl Iterator<Item = &Term> { self.terms.iter() }
    pub fn len(&self) -> usize { self.terms.len() }
    pub fn is_empty(&self) -> bool { self.terms.is_empty() }

    /// Extend the universe with congruence consequences (v0.18 M).
    ///
    /// For each `(a, b)` in `equalities` and each term `t`
    /// currently in the universe, generate `t[a/b]` (substitute
    /// `a` with `b`) and `t[b/a]` (the reverse) and add them to
    /// the universe. This is the lightest-weight form of
    /// congruence-aware E-matching: instead of plumbing the full
    /// EUF state into the matcher, we materialise the congruent
    /// terms up-front so the linear-scan matcher sees them.
    ///
    /// The substitution is structural — `a` is matched
    /// α-equivalent at any subterm position and replaced. Bound-
    /// variable α-renaming is *not* applied; the caller is
    /// responsible for ensuring `a` and `b` are closed terms.
    ///
    /// Idempotent: re-running on a universe that already has the
    /// congruent terms is a no-op (`insert` dedups by
    /// α-equivalence).
    pub fn extend_with_equalities(
        &mut self,
        equalities: &[(Term, Term)],
    ) {
        // Snapshot the universe before the mutating `insert`
        // loop (which needs `&mut self`).  Collect into a
        // `Vec<Term>` rather than cloning the `IndexSet` — a
        // `Vec` of `Arc` handles is a cheap refcount-bump copy,
        // whereas cloning the `IndexSet` would rebuild the
        // hash table.  The `insert` calls below still dedup
        // against the live `self.terms` in O(1).
        let snapshot: Vec<Term> = self.terms.iter().cloned().collect();
        for (a, b) in equalities {
            for t in &snapshot {
                if let Some(t_ab) = substitute_in(t, a, b) {
                    self.insert(t_ab);
                }
                if let Some(t_ba) = substitute_in(t, b, a) {
                    self.insert(t_ba);
                }
            }
        }
    }
}

/// Substitute every α-equivalent occurrence of `from` inside `t`
/// with `to`. Returns `Some(new_t)` when at least one substitution
/// happened, `None` when `t` doesn't contain `from`.
fn substitute_in(t: &Term, from: &Term, to: &Term) -> Option<Term> {
    if t.alpha_eq(from) {
        return Some(to.clone());
    }
    match t.kind() {
        TermInner::Var(_) | TermInner::Const(_) => None,
        TermInner::App(f, x) => {
            let f_sub = substitute_in(f, from, to);
            let x_sub = substitute_in(x, from, to);
            if f_sub.is_some() || x_sub.is_some() {
                let new_f = f_sub.unwrap_or_else(|| f.clone());
                let new_x = x_sub.unwrap_or_else(|| x.clone());
                Term::app(new_f, new_x).ok()
            } else {
                None
            }
        }
        TermInner::Lam(v, body) => {
            substitute_in(body, from, to)
                .map(|new_body| Term::lam((**v).clone(), new_body))
        }
    }
}

#[derive(Clone, Debug)]
pub struct Instantiation {
    pub subst: Vec<(Arc<Var>, Term)>,
}

pub struct EMatcher<'a> {
    universe: &'a TermUniverse,
}

impl<'a> EMatcher<'a> {
    pub fn new(universe: &'a TermUniverse) -> Self { Self { universe } }

    /// Find instantiations of the trigger's bound variables against
    /// terms in the universe. Single-pattern triggers match against
    /// each universe term independently; multi-pattern triggers
    /// require *all* sub-patterns to match consistently.
    pub fn match_trigger(&self, trigger: &Trigger) -> Vec<Instantiation> {
        match &trigger.kind {
            TriggerKind::Single(p) => self
                .universe
                .iter()
                .filter_map(|t| match_one(p, t, &trigger.bound))
                .map(|subst| Instantiation { subst })
                .collect(),
            TriggerKind::Multi(ps) => self.match_multi(ps, &trigger.bound),
        }
    }

    fn match_multi(
        &self,
        patterns: &[Term],
        bound: &[Arc<Var>],
    ) -> Vec<Instantiation> {
        if patterns.is_empty() {
            return Vec::new();
        }
        // Start with all matches of the first pattern; refine via the rest.
        let first: Vec<IndexMap<Arc<Var>, Term>> = self
            .universe
            .iter()
            .filter_map(|t| match_one(&patterns[0], t, bound))
            .map(|v| v.into_iter().collect())
            .collect();
        let mut current = first;
        for p in &patterns[1..] {
            let mut next = Vec::new();
            for candidate in &current {
                for t in self.universe.iter() {
                    let mut merged = candidate.clone();
                    if extend_match(p, t, bound, &mut merged) {
                        next.push(merged);
                    }
                }
            }
            current = next;
            if current.is_empty() {
                break;
            }
        }
        current
            .into_iter()
            .map(|subst| Instantiation { subst: subst.into_iter().collect() })
            .collect()
    }
}

/// Match a single pattern against a single target. Returns `Some(σ)`
/// where σ maps the flex (`bound`) variables to terms.
fn match_one(pattern: &Term, target: &Term, bound: &[Arc<Var>]) -> Option<Vec<(Arc<Var>, Term)>> {
    let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
    if extend_match(pattern, target, bound, &mut sigma) {
        Some(sigma.into_iter().collect())
    } else {
        None
    }
}

fn extend_match(
    pattern: &Term,
    target: &Term,
    bound: &[Arc<Var>],
    sigma: &mut IndexMap<Arc<Var>, Term>,
) -> bool {
    match (pattern.kind(), target.kind()) {
        (TermInner::Var(v), _) if bound.iter().any(|b| **b == **v) => {
            if v.ty != target.type_of() {
                return false;
            }
            if let Some(prev) = sigma.get(v) {
                return prev.alpha_eq(target);
            }
            sigma.insert(v.clone(), target.clone());
            true
        }
        (TermInner::Var(v1), TermInner::Var(v2)) => **v1 == **v2,
        (TermInner::Const(c1), TermInner::Const(c2)) => **c1 == **c2,
        (TermInner::App(f1, a1), TermInner::App(f2, a2)) => {
            extend_match(f1, f2, bound, sigma) && extend_match(a1, a2, bound, sigma)
        }
        (TermInner::Lam(v1, b1), TermInner::Lam(v2, b2)) => {
            v1.ty == v2.ty && extend_match(b1, b2, bound, sigma)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn matches_pattern_against_universe() {
        // pattern: P x (x flex), universe: { P a, P b, Q c }
        let p_const = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let q_const = Term::const_("Q", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_());
        let b = Term::const_("b", int_());
        let c = Term::const_("c", int_());
        let mut u = TermUniverse::new();
        u.insert(Term::app(p_const.clone(), a.clone()).unwrap());
        u.insert(Term::app(p_const.clone(), b.clone()).unwrap());
        u.insert(Term::app(q_const, c).unwrap());

        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let pattern = Term::app(p_const, Term::Var(x.clone())).unwrap();
        let trig = Trigger::single(pattern, vec![x.clone()]);

        let m = EMatcher::new(&u);
        let insts = m.match_trigger(&trig);
        assert_eq!(insts.len(), 2);
        let bound_values: Vec<Term> = insts
            .iter()
            .filter_map(|i| i.subst.iter().find(|(v, _)| **v == *x).map(|(_, t)| t.clone()))
            .collect();
        assert!(bound_values.iter().any(|t| t.alpha_eq(&a)));
        assert!(bound_values.iter().any(|t| t.alpha_eq(&b)));
    }

    #[test]
    fn universe_extend_with_equalities_adds_congruent_terms() {
        // Universe: { P(a) }. Equality: a = b.
        // After extend: { P(a), P(b) }.
        let p_const =
            Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_());
        let b = Term::const_("b", int_());
        let mut u = TermUniverse::new();
        u.insert(Term::app(p_const.clone(), a.clone()).unwrap());
        assert_eq!(u.len(), 1);
        u.extend_with_equalities(&[(a.clone(), b.clone())]);
        let expected_pb = Term::app(p_const, b).unwrap();
        assert!(u.iter().any(|t| t.alpha_eq(&expected_pb)));
        // Original P(a) still present.
        let expected_pa = u.iter().nth(0).unwrap().clone();
        assert!(expected_pa.alpha_eq(&Term::app(
            Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap()),
            a,
        ).unwrap()));
    }

    #[test]
    fn matcher_picks_up_congruent_term_after_extend() {
        // Universe: { P(a) }, equality a = b.
        // Pattern P(x). Before extend: 1 match (x = a).
        // After extend: 2 matches (x = a, x = b).
        let p_const =
            Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_());
        let b = Term::const_("b", int_());
        let mut u = TermUniverse::new();
        u.insert(Term::app(p_const.clone(), a.clone()).unwrap());

        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let pattern =
            Term::app(p_const.clone(), Term::Var(x.clone())).unwrap();
        let trig = Trigger::single(pattern, vec![x.clone()]);

        let insts_before = EMatcher::new(&u).match_trigger(&trig);
        assert_eq!(insts_before.len(), 1);

        u.extend_with_equalities(&[(a, b.clone())]);
        let insts_after = EMatcher::new(&u).match_trigger(&trig);
        assert_eq!(insts_after.len(), 2);
        // One instantiation binds x to b — the equality picked
        // up by extend_with_equalities.
        let bound_values: Vec<Term> = insts_after
            .iter()
            .filter_map(|i| {
                i.subst.iter().find(|(v, _)| **v == *x).map(|(_, t)| t.clone())
            })
            .collect();
        assert!(bound_values.iter().any(|t| t.alpha_eq(&b)));
    }

    #[test]
    fn extend_with_equalities_is_idempotent() {
        let p_const =
            Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_());
        let b = Term::const_("b", int_());
        let mut u = TermUniverse::new();
        u.insert(Term::app(p_const, a.clone()).unwrap());
        u.extend_with_equalities(&[(a.clone(), b.clone())]);
        let after_first = u.len();
        u.extend_with_equalities(&[(a, b)]);
        assert_eq!(u.len(), after_first);
    }

    #[test]
    fn no_match_returns_empty() {
        let p_const = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let q_const = Term::const_("Q", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_());
        let mut u = TermUniverse::new();
        u.insert(Term::app(q_const, a).unwrap());

        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let pattern = Term::app(p_const, Term::Var(x.clone())).unwrap();
        let trig = Trigger::single(pattern, vec![x]);

        let insts = EMatcher::new(&u).match_trigger(&trig);
        assert!(insts.is_empty());
    }
}
