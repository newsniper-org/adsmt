//! Tier 3 — bounded enumerative instantiation.
//!
//! When Tier 1 (Miller-pattern E-matching) and Tier 2 (conflict-
//! based) have both failed to make progress on a quantified
//! formula, the engine falls back to **bounded enumeration**: for
//! every ground term in the [`TermUniverse`] whose sort matches the
//! bound variable, generate the instantiated body.
//!
//! Bounding is by *universe size* — which itself is bounded by the
//! input size — plus an explicit per-call budget so a malicious
//! input can't blow up the round budget.
//!
//! This module is the explicit home of the strategy that used to
//! be inlined as a fallback inside [`crate::ematch`]'s
//! `instantiate_one`. Keeping it separate lets the solver loop
//! escalate strategies in clear order (Tier 1 → 2 → 3 → 4) and
//! lets per-strategy budgets be tuned independently.

use std::sync::Arc;

use adsmt_core::{Term, Var};
use indexmap::IndexMap;

use crate::ematch::TermUniverse;

/// A request to enumerate instantiations for a bound variable over
/// a bounded set of candidate terms.
#[derive(Clone, Debug)]
pub struct EnumerationTask {
    pub var: Arc<Var>,
    pub candidates: Vec<Term>,
}

impl EnumerationTask {
    pub fn new(var: Arc<Var>, candidates: Vec<Term>) -> Self {
        Self { var, candidates }
    }

    pub fn is_bounded(&self, limit: usize) -> bool {
        self.candidates.len() <= limit
    }
}

/// Default per-call enumeration budget. Acts as a safety net so
/// pathological universes don't dominate a `check_sat` round.
pub const DEFAULT_TIER3_BUDGET: usize = 64;

/// Enumerate instantiated bodies for `∀ var. body` by walking every
/// `universe` term whose type matches `var.ty`, applying the
/// substitution `{var ↦ t}` and yielding the resulting body.
///
/// Candidates are deduplicated by their string representation
/// (sufficient for our use — variables come from a stable parser
/// pipeline and printer is total). The result is truncated to
/// `budget` entries; pass [`DEFAULT_TIER3_BUDGET`] for the
/// usual setting.
pub fn enumerate(
    var: &Var,
    body: &Term,
    universe: &TermUniverse,
    budget: usize,
) -> Vec<Term> {
    if budget == 0 {
        return Vec::new();
    }
    let v_arc = Arc::new(var.clone());
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut out: Vec<Term> = Vec::new();
    let mut matched_sort = false;
    for t in universe.iter() {
        if t.type_of() != var.ty {
            continue;
        }
        matched_sort = true;
        let key = t.to_string();
        if !seen.insert(key) {
            continue;
        }
        let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
        sigma.insert(v_arc.clone(), t.clone());
        if let Ok(instantiated) = body.subst(&sigma) {
            out.push(instantiated);
            if out.len() >= budget {
                break;
            }
        }
    }
    // SOUNDNESS — fresh witness for an empty-domain sort. When the bound
    // variable's SORT has NO ground term in the universe, the loop above
    // instantiates NOTHING, and the engine's saturation rule ("no new
    // instantiations ⇒ sat") would then conclude a DECISIVE `sat` it cannot
    // justify: e.g. `∀x:U. (and (p x) (not (p x)))` with no ground `U`-term is
    // `∀x. false`, UNSAT over a non-empty sort, yet never instantiated to expose
    // the contradiction (filed by verus-fork 2026-06-21). SMT sorts are
    // non-empty, so a fresh constant denotes SOME element of `U`, and
    // `∀x.body ⊨ body[fresh]` is a SOUND consequence — adding it can only ever
    // surface an existing unsat, never fabricate one (a satisfiable body stays
    // satisfiable: the fresh point completes freely). The name is sort-keyed +
    // deterministic, so the instance is identical every round (re-inserted into
    // the engine's `IndexSet` and deduped → the fixpoint still terminates). Only
    // fires when the sort is otherwise un-witnessed; a sort with ground terms
    // enumerates over those as before.
    if !matched_sort {
        let fresh = Term::const_(&format!("!mbqi-fresh!{}", var.ty), var.ty.clone());
        let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
        sigma.insert(v_arc.clone(), fresh);
        if let Ok(instantiated) = body.subst(&sigma) {
            out.push(instantiated);
        }
    }
    out
}

/// Drain candidates from `task`, applying each as an instantiation
/// of `body` for `task.var`. Equivalent to [`enumerate`] but
/// pre-bound — used when a caller already curated the candidate
/// list (for example a theory-specific abducible source).
pub fn enumerate_task(task: &EnumerationTask, body: &Term, budget: usize) -> Vec<Term> {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut out: Vec<Term> = Vec::new();
    for t in &task.candidates {
        if t.type_of() != task.var.ty {
            continue;
        }
        let key = t.to_string();
        if !seen.insert(key) {
            continue;
        }
        let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
        sigma.insert(task.var.clone(), t.clone());
        if let Ok(instantiated) = body.subst(&sigma) {
            out.push(instantiated);
            if out.len() >= budget {
                break;
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type {
        Type::const_("Int", Kind::Type)
    }

    #[test]
    fn enumerates_terms_of_matching_sort() {
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let c_bool = Term::var("c", Type::bool_());
        let mut u = TermUniverse::new();
        u.insert(a.clone());
        u.insert(b.clone());
        u.insert(c_bool); // wrong sort — must be skipped

        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x.clone()))).unwrap();

        let insts = enumerate(&x, &body, &u, DEFAULT_TIER3_BUDGET);
        assert_eq!(insts.len(), 2);
        let strs: Vec<String> = insts.iter().map(|t| t.to_string()).collect();
        assert!(strs.iter().any(|s| s.contains('a')));
        assert!(strs.iter().any(|s| s.contains('b')));
    }

    #[test]
    fn respects_budget() {
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let mut u = TermUniverse::new();
        for i in 0..10 {
            u.insert(Term::var(&format!("v{i}"), int_()));
        }

        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x.clone()))).unwrap();

        let insts = enumerate(&x, &body, &u, 3);
        assert_eq!(insts.len(), 3);
    }

    #[test]
    fn zero_budget_yields_empty() {
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let mut u = TermUniverse::new();
        u.insert(Term::var("a", int_()));
        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x.clone()))).unwrap();
        let insts = enumerate(&x, &body, &u, 0);
        assert!(insts.is_empty());
    }

    #[test]
    fn enumerate_task_curated_candidates() {
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x.clone()))).unwrap();
        let task = EnumerationTask::new(Arc::new(x), vec![a, b]);
        let insts = enumerate_task(&task, &body, DEFAULT_TIER3_BUDGET);
        assert_eq!(insts.len(), 2);
    }

    #[test]
    fn dedup_by_string_representation() {
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::var("a", int_());
        let mut u = TermUniverse::new();
        u.insert(a.clone());
        u.insert(a.clone()); // same term again
        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x.clone()))).unwrap();
        let insts = enumerate(&x, &body, &u, DEFAULT_TIER3_BUDGET);
        // Universe.insert already dedups by alpha_eq; just confirm
        // we don't emit duplicates either way.
        assert_eq!(insts.len(), 1);
    }
}
