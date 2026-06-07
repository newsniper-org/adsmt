//! Polite theory combination.
//!
//! In our framework Nelson-Oppen is the *trivial* case where every
//! theory's politeness witness is ω. Each theory provides a
//! `cardinality_witness` and the combination loop reconciles them: if
//! the intersection of cardinality bounds for a shared sort is empty,
//! the combined system is unsat with a [`PoliteWitness`] conflict.
//!
//! v0.1 ships the registry and the cardinality-reconciliation step;
//! the full DPLL(T) loop, arrangement guessing, and equality
//! propagation arrive in v0.3.

use adsmt_cert::witness::PoliteWitness;
use adsmt_core::{Term, Type};

use crate::trait_::{CheckResult, Literal, Theory};

/// A registry of theories participating in combination.
#[derive(Default)]
pub struct Combination {
    theories: Vec<Box<dyn Theory>>,
}


impl Combination {
    pub fn new() -> Self { Self::default() }

    pub fn register(&mut self, t: Box<dyn Theory>) {
        self.theories.push(t);
    }

    pub fn theories(&self) -> &[Box<dyn Theory>] { &self.theories }
    pub fn theories_mut(&mut self) -> &mut [Box<dyn Theory>] { &mut self.theories }

    /// rc.25 (T0''') — fan the wall-clock deadline out to every
    /// registered theory before a [`Self::check`] round, so
    /// theories with unbounded internal fixpoints (UF congruence
    /// closure) can yield to the budget.
    pub fn set_deadline(&mut self, deadline: Option<std::time::Instant>) {
        for t in &mut self.theories {
            t.set_deadline(deadline);
        }
    }

    /// Broadcast an assertion to every theory that handles its sort.
    ///
    /// For equality literals `(= a b)` the *operand* sort is the
    /// routing key — that's the sort the equality is about, even
    /// though the formula itself is Bool. This makes the Datatypes
    /// and Arrays theories see equalities about their elements
    /// without having to special-case Bool.
    pub fn assert(&mut self, lit: Literal) -> Vec<(String, crate::trait_::AssertResult)> {
        let routing_sort = if let Some((a, _)) = lit.term.dest_eq() {
            a.type_of()
        } else {
            lit.term.type_of()
        };
        let mut out = Vec::new();
        for t in &mut self.theories {
            if t.handles_sort(&routing_sort) {
                let r = t.assert(lit.clone());
                out.push((t.name().to_string(), r));
            }
        }
        out
    }

    /// Run `check` on each theory with Nelson-Oppen equality
    /// propagation, followed by polite cardinality enforcement
    /// (v0.9): if any sort's disequality clique exceeds its
    /// cardinality bound, the combined system is unsat.
    ///
    /// Order per round:
    /// 1. `check()` every theory (closures, internal propagation).
    /// 2. Gather `derive_equalities` from every theory.
    /// 3. Re-broadcast new ones via `assert`; fixpoint → step 4.
    /// 4. For each registered sort, compare its max disequality
    ///    clique against the polite cardinality witness. If the
    ///    clique exceeds the bound → unsat with a polite witness.
    pub fn check(&mut self) -> CombinedCheck {
        const PROP_BUDGET: usize = 8;
        let mut seen: Vec<(Term, Term)> = Vec::new();

        for _round in 0..PROP_BUDGET {
            // (1) Individual theory checks first.
            for i in 0..self.theories.len() {
                let name = self.theories[i].name().to_string();
                match self.theories[i].check() {
                    CheckResult::Sat => continue,
                    CheckResult::Unsat { witness } => {
                        return CombinedCheck::Unsat { theory: name, witness };
                    }
                    CheckResult::Unknown { reason } => {
                        return CombinedCheck::Unknown { theory: name, reason };
                    }
                }
            }

            // (2) Gather derived equalities, excluding ones already seen.
            let mut gathered: Vec<(Term, Term)> = Vec::new();
            for t in &self.theories {
                for eq in t.derive_equalities() {
                    if !seen.iter().any(|(a, b)| {
                        (a.alpha_eq(&eq.0) && b.alpha_eq(&eq.1))
                            || (a.alpha_eq(&eq.1) && b.alpha_eq(&eq.0))
                    }) {
                        gathered.push(eq.clone());
                    }
                }
            }
            if gathered.is_empty() {
                // (4) Cardinality enforcement: gather disequalities
                // from every theory, group by operand sort, and check
                // each sort's clique size against its polite witness.
                if let Some(unsat) = self.enforce_cardinality() {
                    return unsat;
                }
                return CombinedCheck::Sat;
            }

            // (3) Re-broadcast.
            for (a, b) in &gathered {
                seen.push((a.clone(), b.clone()));
                if let Ok(eq_term) = Term::mk_eq(a.clone(), b.clone())
                    && let Ok(lit) = crate::trait_::Literal::positive(eq_term) {
                        let _ = self.assert(lit);
                    }
            }
        }

        CombinedCheck::Unknown {
            theory: "polite".into(),
            reason: "Nelson-Oppen propagation budget exhausted".into(),
        }
    }

    /// Polite combination cardinality enforcement (v0.9).
    fn enforce_cardinality(&self) -> Option<CombinedCheck> {
        use std::collections::HashMap;
        // Gather all asserted disequalities, grouped by operand sort.
        let mut diseqs_by_sort: HashMap<String, Vec<(Term, Term)>> = HashMap::new();
        for t in &self.theories {
            for (a, b) in t.derive_disequalities() {
                let sort = a.type_of().to_string();
                diseqs_by_sort.entry(sort).or_default().push((a, b));
            }
        }
        // For each sort with a finite cardinality bound, check the
        // disequality clique size.
        for (sort_str, pairs) in &diseqs_by_sort {
            let sort_ty = Type::const_(sort_str, adsmt_core::Kind::Type);
            let bound = self
                .theories
                .iter()
                .filter(|t| t.handles_sort(&sort_ty))
                .filter_map(|t| t.cardinality_witness(&sort_ty).upper_bound)
                .min();
            let Some(bound) = bound else { continue; };
            let clique = max_disequality_clique(pairs, bound as usize + 1);
            if clique > bound as usize {
                return Some(CombinedCheck::Unsat {
                    theory: "polite".into(),
                    witness: adsmt_cert::witness::TheoryWitness::Polite(
                        adsmt_cert::witness::PoliteWitness {
                            sort: sort_str.clone(),
                            upper_bound: Some(bound),
                        },
                    ),
                });
            }
        }
        None
    }

    /// Reconcile cardinality witnesses for a sort across all theories.
    ///
    /// If no theory provides a finite bound the sort is treated as ω.
    /// Otherwise the minimum of the finite bounds is the reconciled
    /// upper bound; the witness records which theory imposed it.
    pub fn reconcile_cardinality(&self, sort: &Type) -> CardinalityReconciliation {
        let mut tightest: Option<(String, u64)> = None;
        let mut sources: Vec<(String, Option<u64>)> = Vec::new();
        for t in &self.theories {
            if !t.handles_sort(sort) {
                continue;
            }
            let w = t.cardinality_witness(sort);
            sources.push((t.name().to_string(), w.upper_bound));
            if let Some(n) = w.upper_bound {
                match tightest.as_ref() {
                    None => tightest = Some((t.name().to_string(), n)),
                    Some((_, m)) if n < *m => {
                        tightest = Some((t.name().to_string(), n));
                    }
                    _ => {}
                }
            }
        }
        CardinalityReconciliation {
            sort_name: format!("{sort}"),
            tightest,
            sources,
        }
    }

    /// v0.19 C.5 — reconcile cardinality witnesses across **all
    /// sorts** every theory handles. Returns one
    /// [`CardinalityReconciliation`] per sort.
    ///
    /// Two theories disagreeing on whether a sort is finite is a
    /// *cardinality disagreement*. The disagreement isn't an
    /// unsat by itself (a missing witness is treated as ω), but
    /// it flags a soundness-relevant divergence callers may want
    /// to log.
    pub fn reconcile_all_sorts(&self) -> Vec<CardinalityReconciliation> {
        use std::collections::BTreeSet;
        // Distinct (sort name + sort type) pairs across all
        // theories. We canonicalise on the sort's Display form
        // so two theories agree iff they report the same sort
        // string.
        let mut sorts: BTreeSet<String> = BTreeSet::new();
        let mut sort_terms: std::collections::HashMap<String, Type> =
            std::collections::HashMap::new();
        for t in &self.theories {
            // We can only enumerate sorts a theory's
            // `cardinality_witness` would emit if we know them
            // up-front. v0.18 has no introspection API yet, so
            // we ask each theory about a small canonical set:
            // the bool / int / real / bv8 / bv16 sorts plus any
            // sort that has appeared in an assertion.
            for s in [
                Type::bool_(),
                Type::const_("Int", adsmt_core::Kind::Type),
                Type::const_("Real", adsmt_core::Kind::Type),
                Term::bv_sort(8),
                Term::bv_sort(16),
            ] {
                if t.handles_sort(&s) {
                    let name = s.to_string();
                    sorts.insert(name.clone());
                    sort_terms.entry(name).or_insert(s);
                }
            }
        }
        sorts
            .into_iter()
            .filter_map(|name| {
                sort_terms.get(&name).map(|s| self.reconcile_cardinality(s))
            })
            .collect()
    }

    /// v0.19 C.5 — emit one [`CardinalityDisagreement`] per
    /// sort where two theories report different finite
    /// upper-bounds (or where one says finite and another says
    /// ω). Returns an empty vector when every sort is consistent.
    ///
    /// Note: disagreement is **distinct from unsat**. The
    /// reconciled bound is the minimum of the finite ones
    /// (already done by `reconcile_cardinality`); the
    /// disagreement vector is purely diagnostic, surfacing when
    /// the reconciliation was non-trivial.
    pub fn detect_cardinality_disagreements(&self) -> Vec<CardinalityDisagreement> {
        self.reconcile_all_sorts()
            .into_iter()
            .filter_map(|recon| {
                let distinct_finite: std::collections::BTreeSet<u64> = recon
                    .sources
                    .iter()
                    .filter_map(|(_, b)| *b)
                    .collect();
                let any_infinite =
                    recon.sources.iter().any(|(_, b)| b.is_none());
                if distinct_finite.len() > 1
                    || (distinct_finite.len() == 1 && any_infinite)
                {
                    Some(CardinalityDisagreement {
                        sort_name: recon.sort_name,
                        per_theory: recon.sources,
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Drop all theory state.
    pub fn reset(&mut self) {
        for t in &mut self.theories {
            t.reset();
        }
    }

    pub fn push(&mut self) {
        for t in &mut self.theories {
            t.push();
        }
    }

    pub fn pop(&mut self, levels: u32) {
        for t in &mut self.theories {
            t.pop(levels);
        }
    }
}

/// Find the size of the largest clique in the disequality graph
/// induced by `pairs`, bounded by `limit`. NP-hard in general but
/// SMT-typical inputs have tiny graphs.
fn max_disequality_clique(pairs: &[(Term, Term)], limit: usize) -> usize {
    use std::collections::HashSet;
    // Vertex set: every term appearing in any pair.
    //
    // rc.24 (e'''.3) — dedup-on-build through a `HashSet<Term>`
    // scratch rather than the prior
    // `vertices.iter().any(|v| v.alpha_eq(a))` linear scan.
    // `vertices` stays a `Vec<Term>` because the clique walk
    // below indexes it positionally; only the dedup probe
    // moves to O(1) on the rc.10 hash-cons handle.  Insertion
    // order is unchanged, so the greedy clique traversal is
    // bit-identical.
    let mut vertices: Vec<Term> = Vec::new();
    let mut seen: HashSet<Term> = HashSet::new();
    for (a, b) in pairs {
        if seen.insert(a.clone()) { vertices.push(a.clone()); }
        if seen.insert(b.clone()) { vertices.push(b.clone()); }
    }
    // Adjacency check: are u, v in an asserted disequality?
    let adj = |u: &Term, v: &Term| -> bool {
        pairs.iter().any(|(a, b)| {
            (a.alpha_eq(u) && b.alpha_eq(v)) || (a.alpha_eq(v) && b.alpha_eq(u))
        })
    };
    // Greedy + Bron-Kerbosch-lite, bounded by `limit`.
    let mut best = 0usize;
    fn extend(
        cur: &mut Vec<usize>,
        candidates: HashSet<usize>,
        vertices: &[Term],
        adj: &impl Fn(&Term, &Term) -> bool,
        best: &mut usize,
        limit: usize,
    ) {
        if cur.len() > *best { *best = cur.len(); }
        if *best >= limit { return; }
        for &v in &candidates {
            cur.push(v);
            let new_candidates: HashSet<usize> = candidates
                .iter()
                .copied()
                .filter(|&u| u != v && adj(&vertices[u], &vertices[v]))
                .collect();
            extend(cur, new_candidates, vertices, adj, best, limit);
            cur.pop();
        }
    }
    let all: HashSet<usize> = (0..vertices.len()).collect();
    extend(&mut Vec::new(), all, &vertices, &adj, &mut best, limit);
    best
}

#[derive(Clone, Debug)]
pub enum CombinedCheck {
    Sat,
    Unsat { theory: String, witness: adsmt_cert::witness::TheoryWitness },
    Unknown { theory: String, reason: String },
}

/// Result of [`Combination::reconcile_cardinality`].
#[derive(Clone, Debug)]
pub struct CardinalityReconciliation {
    pub sort_name: String,
    /// Tightest finite bound observed, with the theory that imposed it.
    /// `None` means every theory said ω.
    pub tightest: Option<(String, u64)>,
    /// All witnesses observed, in registration order.
    pub sources: Vec<(String, Option<u64>)>,
}

impl CardinalityReconciliation {
    pub fn as_witness(&self) -> PoliteWitness {
        PoliteWitness {
            sort: self.sort_name.clone(),
            upper_bound: self.tightest.as_ref().map(|(_, n)| *n),
        }
    }
}

/// v0.19 C.5 — diagnostic record for a sort where two theories
/// disagreed on the cardinality bound. Reconciliation still
/// produces a valid (minimum-finite) bound, but the
/// disagreement may indicate a latent soundness divergence
/// worth surfacing in logs.
#[derive(Clone, Debug)]
pub struct CardinalityDisagreement {
    pub sort_name: String,
    /// All witness reports observed, in theory-registration order.
    pub per_theory: Vec<(String, Option<u64>)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cert::witness::TheoryWitness;
    use adsmt_core::{Kind, Type};

    /// Dummy theory that always asserts `cardinality_witness == bound`.
    struct ConstCard {
        name_: &'static str,
        bound: Option<u64>,
    }

    impl Theory for ConstCard {
        fn name(&self) -> &'static str { self.name_ }
        fn handles_sort(&self, _: &Type) -> bool { true }
        fn assert(&mut self, _: Literal) -> crate::trait_::AssertResult {
            crate::trait_::AssertResult::Accepted
        }
        fn check(&mut self) -> CheckResult { CheckResult::Sat }
        fn explain(&self) -> Option<TheoryWitness> { None }
        fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
            PoliteWitness { sort: format!("{sort}"), upper_bound: self.bound }
        }
        fn reset(&mut self) {}
    }

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn reconcile_omega_when_all_infinite() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: None }));
        c.register(Box::new(ConstCard { name_: "B", bound: None }));
        let r = c.reconcile_cardinality(&int_());
        assert!(r.tightest.is_none());
    }

    #[test]
    fn reconcile_picks_smallest_finite_bound() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: Some(8) }));
        c.register(Box::new(ConstCard { name_: "B", bound: Some(3) }));
        c.register(Box::new(ConstCard { name_: "C", bound: None }));
        let r = c.reconcile_cardinality(&int_());
        assert_eq!(r.tightest, Some(("B".into(), 3)));
        assert_eq!(r.sources.len(), 3);
    }

    #[test]
    fn check_returns_sat_when_all_sat() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: None }));
        assert!(matches!(c.check(), CombinedCheck::Sat));
    }

    #[test]
    fn reconcile_all_sorts_returns_one_entry_per_sort() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: Some(8) }));
        let recs = c.reconcile_all_sorts();
        // At least Int (covered by ConstCard's handles_sort).
        assert!(!recs.is_empty());
    }

    #[test]
    fn detect_cardinality_disagreements_empty_when_all_agree() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: Some(8) }));
        c.register(Box::new(ConstCard { name_: "B", bound: Some(8) }));
        // Both theories report the same bound — no disagreement.
        assert!(c.detect_cardinality_disagreements().is_empty());
    }

    #[test]
    fn detect_cardinality_disagreements_flags_distinct_bounds() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: Some(8) }));
        c.register(Box::new(ConstCard { name_: "B", bound: Some(3) }));
        let diagn = c.detect_cardinality_disagreements();
        assert!(!diagn.is_empty(), "expected disagreement for distinct bounds");
        // The reconciled minimum is still 3 (preserved by
        // reconcile_cardinality).
        let recs = c.reconcile_all_sorts();
        for r in recs {
            if let Some((_, n)) = r.tightest {
                assert_eq!(n, 3);
            }
        }
    }

    #[test]
    fn detect_disagreements_flags_finite_vs_infinite_mix() {
        let mut c = Combination::new();
        c.register(Box::new(ConstCard { name_: "A", bound: Some(8) }));
        c.register(Box::new(ConstCard { name_: "B", bound: None }));
        let diagn = c.detect_cardinality_disagreements();
        assert!(
            !diagn.is_empty(),
            "expected disagreement for finite vs infinite mix",
        );
    }
}
