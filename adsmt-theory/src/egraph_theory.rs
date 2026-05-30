//! v0.23 23B.2 — `Theory` wrapper around `adsmt_quant::egraph::EGraph`.
//!
//! Optional theory the engine can register alongside the
//! existing UF / LIA / LRA / BV / Arrays / Datatypes / Polite
//! family. The EGraph carries the hash-consed + congruence-
//! closed view of every term mentioned in positive equality
//! assertions; on `check()` it yields the derived class-
//! equivalence pairs as `derive_equalities` so peer theories
//! (and the Nelson-Oppen propagation loop in
//! `polite::Combination`) see the closure.
//!
//! The wrapper is intentionally *additive* — it does NOT
//! replace UF (UF carries its own union-find for the polite
//! disequality clique check). Both can be registered
//! simultaneously; the EGraph contribution is the congruence
//! cascade across function applications that UF only fires on
//! literal-pair matches.

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};
use adsmt_quant::egraph::EGraph;

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

/// Engine-facing `Theory` wrapper around an EGraph.
#[derive(Default)]
pub struct EgraphTheory {
    graph: EGraph,
    /// Pairs of `(a, b)` recorded as positive equality
    /// assertions. Used to drive the class-equivalence walk
    /// in [`Self::rebuild_derived_eqs`].
    asserted_eqs: Vec<(Term, Term)>,
    /// Cached output of the last `rebuild_derived_eqs` call;
    /// served by [`Theory::derive_equalities`] without
    /// requiring `&mut self` on the trait method.
    derived_eqs: Vec<(Term, Term)>,
    /// Snapshot stack for `push`/`pop` — each entry holds
    /// `(asserted_eqs.len(), derived_eqs.len())` at the moment
    /// of the matching push.
    scope_stack: Vec<(usize, usize)>,
}

impl EgraphTheory {
    pub fn new() -> Self { Self::default() }

    /// Direct access to the inner graph for tests / engine
    /// integration helpers (e.g. surfacing
    /// `EGraph::as_universe()` to the quantifier instantiation
    /// pass).
    pub fn graph(&self) -> &EGraph { &self.graph }

    /// Mutable access — same use cases as [`Self::graph`] but
    /// for the rare cases that need to drive merges out of band
    /// (currently none in tree).
    pub fn graph_mut(&mut self) -> &mut EGraph { &mut self.graph }

    /// Recompute `derived_eqs` from the current EGraph closure.
    /// Walks every operand recorded in `asserted_eqs`, groups
    /// by class representative, and emits pairwise edges
    /// between distinct α-shapes inside the same class.
    /// Also surfaces application-level congruences by walking
    /// the full universe and grouping by find().
    fn rebuild_derived_eqs(&mut self) {
        use std::collections::HashMap;
        // Collect every distinct (α-eq) term currently in the
        // graph via the universe projection.
        let universe = self.graph.as_universe();
        let universe_terms: Vec<Term> = universe.iter().cloned().collect();
        // For each universe term, re-add it to recover its id.
        // `add` is idempotent — no new node is created when the
        // term already exists — and returns the class rep.
        let mut per_class: HashMap<u32, Vec<Term>> = HashMap::new();
        for t in &universe_terms {
            let id = self.graph.add(t);
            // We can't read the inner u32 of ENodeId directly,
            // but we can use the stable equivalence-check.
            // Bucket by walking and matching find() against an
            // anchor term per bucket.
            let mut placed = false;
            for (_, members) in per_class.iter_mut() {
                let anchor_id = self.graph.add(&members[0]);
                if self.graph.equivalent(anchor_id, id) {
                    members.push(t.clone());
                    placed = true;
                    break;
                }
            }
            if !placed {
                let key = per_class.len() as u32;
                per_class.insert(key, vec![t.clone()]);
            }
        }
        let mut out = Vec::new();
        for terms in per_class.values() {
            if terms.len() < 2 { continue; }
            for i in 1..terms.len() {
                if !terms[0].alpha_eq(&terms[i]) {
                    out.push((terms[0].clone(), terms[i].clone()));
                }
            }
        }
        self.derived_eqs = out;
    }
}

impl Theory for EgraphTheory {
    fn name(&self) -> &'static str { "EGraph" }

    fn handles_sort(&self, _ty: &Type) -> bool {
        // Sort-agnostic — congruence works over any term.
        true
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        let Some((a, b)) = lit.term.dest_eq() else {
            return AssertResult::Ignored;
        };
        if !lit.polarity {
            // Disequalities don't drive congruence; ignore so UF
            // / Arrays / Datatypes handle them.
            return AssertResult::Ignored;
        }
        let id_a = self.graph.add(&a);
        let id_b = self.graph.add(&b);
        self.graph.merge(id_a, id_b);
        self.asserted_eqs.push((a, b));
        self.rebuild_derived_eqs();
        AssertResult::Accepted
    }

    fn check(&mut self) -> CheckResult { CheckResult::Sat }

    fn explain(&self) -> Option<TheoryWitness> { None }

    fn derive_equalities(&self) -> Vec<(Term, Term)> {
        self.derived_eqs.clone()
    }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        // The EGraph itself is stably infinite over every sort
        // (no constraint on element count). Defer to peer
        // theories for tighter bounds.
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn push(&mut self) {
        self.graph.push();
        self.scope_stack
            .push((self.asserted_eqs.len(), self.derived_eqs.len()));
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            self.graph.pop(1);
            if let Some((n_assert, n_derived)) = self.scope_stack.pop() {
                self.asserted_eqs.truncate(n_assert);
                self.derived_eqs.truncate(n_derived);
            }
        }
    }

    fn reset(&mut self) {
        self.graph = EGraph::new();
        self.asserted_eqs.clear();
        self.derived_eqs.clear();
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn assert_positive_equality_merges_classes() {
        let mut th = EgraphTheory::new();
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let eq = Term::mk_eq(a.clone(), b.clone()).unwrap();
        let r = th.assert(Literal::positive(eq).unwrap());
        assert!(matches!(r, AssertResult::Accepted));
        // The two operands now sit in the same E-class.
        let id_a = th.graph_mut().add(&a);
        let id_b = th.graph_mut().add(&b);
        assert!(th.graph().equivalent(id_a, id_b));
    }

    #[test]
    fn assert_disequality_is_ignored() {
        let mut th = EgraphTheory::new();
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let eq = Term::mk_eq(a, b).unwrap();
        let r = th.assert(Literal::negative(eq).unwrap());
        assert!(matches!(r, AssertResult::Ignored));
    }

    #[test]
    fn derive_equalities_surfaces_congruent_function_applications() {
        // (= a b) → derive (f a) ≡ (f b).
        let mut th = EgraphTheory::new();
        let f = Term::const_("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let fa = Term::app(f.clone(), a.clone()).unwrap();
        let fb = Term::app(f, b.clone()).unwrap();
        // Insert applications first so they're present in the
        // graph for the cascade to pick up.
        let _ = th.graph_mut().add(&fa);
        let _ = th.graph_mut().add(&fb);
        let eq_ab = Term::mk_eq(a, b).unwrap();
        let _ = th.assert(Literal::positive(eq_ab).unwrap());
        // The cascade should have equated (f a) and (f b); the
        // class-walk surfaces them as a derived pair.
        let derived = th.derive_equalities();
        let has_fa_fb = derived.iter().any(|(x, y)| {
            (x.alpha_eq(&fa) && y.alpha_eq(&fb))
                || (x.alpha_eq(&fb) && y.alpha_eq(&fa))
        });
        assert!(has_fa_fb, "expected (f a, f b) in derived pairs: {derived:?}");
    }

    #[test]
    fn push_pop_restores_asserted_pair_count() {
        let mut th = EgraphTheory::new();
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let c = Term::var("c", int_());
        let _ = th.assert(Literal::positive(Term::mk_eq(a, b).unwrap()).unwrap());
        th.push();
        let _ = th.assert(Literal::positive(Term::mk_eq(
            Term::var("b", int_()),
            c,
        ).unwrap()).unwrap());
        assert_eq!(th.asserted_eqs.len(), 2);
        th.pop(1);
        assert_eq!(th.asserted_eqs.len(), 1);
    }
}
