//! Public `Solver` API.

use adsmt_abduce::abducible::AbducibleSet;
use adsmt_abduce::sld::SldEngine;
use adsmt_abduce::workflow::AbductionState;
use adsmt_abduce::{minimize, rank_candidates, MinimizePolicy};
use adsmt_cert::CertBuilder;
use adsmt_core::Term;
use adsmt_theory::arrays::Arrays;
use adsmt_theory::bv::Bv;
use adsmt_theory::datatypes::Datatypes;
use adsmt_theory::polite::Combination;
use adsmt_theory::uf::Uf;

use crate::bool_solver::{dpll, BoolResult};
use crate::cnf::{flatten_to_clauses, Clause, Lit};
use crate::dpllt::{self, LoopOutcome};
use crate::result::{Abductive, SatResult};
use crate::state::Scope;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ProofMode { None, Always }

pub struct Solver {
    scopes: Vec<Scope>,
    theories: Combination,
    abducibles: AbducibleSet,
    abduction_state: AbductionState,
    cert_builder: CertBuilder,
    proof_mode: ProofMode,
}

impl Default for Solver {
    fn default() -> Self {
        let mut theories = Combination::new();
        // v0.3 activates UF/Arrays/Datatypes by default. LinArith
        // remains a placeholder until v0.5 brings Simplex.
        theories.register(Box::new(Uf::new()));
        theories.register(Box::new(Datatypes::new()));
        theories.register(Box::new(Arrays::new()));
        theories.register(Box::new(Bv::new()));
        Self {
            scopes: vec![Scope::new()],
            theories,
            abducibles: AbducibleSet::new(),
            abduction_state: AbductionState::new(),
            cert_builder: CertBuilder::new(),
            proof_mode: ProofMode::None,
        }
    }
}

impl Solver {
    pub fn new() -> Self { Self::default() }

    pub fn with_proof_mode(mut self, mode: ProofMode) -> Self {
        self.proof_mode = mode;
        self
    }

    pub fn proof_mode(&self) -> ProofMode { self.proof_mode }

    pub fn register_theory(&mut self, t: Box<dyn adsmt_theory::trait_::Theory>) {
        self.theories.register(t);
    }

    /// Declare a datatype to the solver's `Datatypes` theory.
    /// Returns `true` if the declaration was accepted, `false` if no
    /// `Datatypes` theory was registered.
    pub fn declare_datatype(
        &mut self,
        decl: adsmt_theory::datatypes::DatatypeDecl,
    ) -> bool {
        for t in self.theories.theories_mut() {
            if t.name() != "Datatypes" { continue; }
            if let Some(any) = t.as_any_mut() {
                if let Some(dt) = any.downcast_mut::<adsmt_theory::datatypes::Datatypes>() {
                    dt.declare(decl);
                    return true;
                }
            }
        }
        false
    }

    pub fn register_abducible(&mut self, a: adsmt_abduce::Abducible) {
        self.abducibles.insert(a);
    }

    /// Assert `t` as a positive literal.
    pub fn assert(&mut self, t: Term) {
        self.assert_with_polarity(t, true);
    }

    /// Assert `t` as a negative literal (equivalent to asserting `¬t`).
    pub fn assert_negated(&mut self, t: Term) {
        self.assert_with_polarity(t, false);
    }

    /// Assert `t` with explicit polarity.
    pub fn assert_with_polarity(&mut self, t: Term, polarity: bool) {
        self.scopes.last_mut().expect("base scope").assert(t, polarity);
    }

    pub fn push(&mut self) {
        self.scopes.push(Scope::new());
        self.theories.push();
    }

    pub fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if self.scopes.len() > 1 {
                self.scopes.pop();
            }
        }
        self.theories.pop(levels);
    }

    pub fn reset(&mut self) {
        self.scopes.clear();
        self.scopes.push(Scope::new());
        self.theories.reset();
        self.abduction_state = AbductionState::new();
        self.cert_builder = CertBuilder::new();
    }

    /// Collected (atom, polarity) literals across every active scope,
    /// plus promoted abductive hypotheses (which live at Level 0,
    /// asserted positively).
    pub fn all_literals(&self) -> Vec<(Term, bool)> {
        let mut out: Vec<(Term, bool)> = Vec::new();
        for h in self.abduction_state.accepted() {
            out.push((h.hypothesis.clone(), true));
        }
        for sc in &self.scopes {
            out.extend(sc.literals.iter().cloned());
        }
        out
    }

    /// Convenience: positive-only assertions (for compatibility with
    /// pre-polarity v0.1 callers).
    pub fn all_assertions(&self) -> Vec<Term> {
        self.all_literals()
            .into_iter()
            .filter_map(|(t, p)| if p { Some(t) } else { None })
            .collect()
    }

    pub fn check_sat(&mut self) -> SatResult {
        const QUANTIFIER_ROUNDS: usize = 3;

        // v0.3 quantifier loop: at each round, partition asserted
        // formulas into quantifiers and ground, then run the ground
        // solver. If Sat, run a Miller-pattern E-matching pass and
        // add fresh instantiations as ground assertions; loop again
        // until either fixpoint or the round budget is exhausted.
        let mut instantiations: Vec<Term> = Vec::new();
        for _round in 0..QUANTIFIER_ROUNDS {
            let mut combined = self.all_literals();
            for inst in &instantiations {
                combined.push((inst.clone(), true));
            }
            let outcome = self.check_ground(&combined);
            match outcome {
                SatResult::Sat => {
                    // Try quantifier instantiation; if no new
                    // instances, we're done at Sat.
                    let (quants, rest) = crate::quant::partition_quantifiers(&combined);
                    if quants.is_empty() {
                        return SatResult::Sat;
                    }
                    let universe = crate::quant::collect_universe(&rest);
                    let prev = instantiations.len();
                    for (var, body) in &quants {
                        for inst in crate::quant::instantiate_one(var, body, &universe) {
                            if !instantiations.iter().any(|t| t.alpha_eq(&inst)) {
                                instantiations.push(inst);
                            }
                        }
                    }
                    if instantiations.len() == prev {
                        return SatResult::Sat;
                    }
                    // else loop with the extended assertion set
                }
                other => return other,
            }
        }
        SatResult::Unknown {
            reason: format!("quantifier instantiation budget ({QUANTIFIER_ROUNDS} rounds) exhausted"),
        }
    }

    /// Ground (quantifier-free) reasoning over the given literals.
    /// Internal helper used by both the surface `check_sat` and the
    /// quantifier-instantiation loop.
    fn check_ground(&mut self, lits: &[(Term, bool)]) -> SatResult {
        // Strip quantifier asserts from the ground path — they're
        // handled by the surrounding instantiation loop.
        let (_quants, lits): (Vec<_>, Vec<_>) = lits
            .iter()
            .cloned()
            .partition(|(t, p)| *p && t.dest_forall().is_some());
        // (1) Decompose every asserted (term, polarity) into CNF clauses.
        let mut clauses: Vec<Clause> = Vec::new();
        let lits = lits;
        for (term, polarity) in &lits {
            let asserted = if *polarity {
                term.clone()
            } else {
                match Term::mk_not(term.clone()) {
                    Ok(t) => t,
                    Err(_) => {
                        return SatResult::Unknown {
                            reason: format!(
                                "non-Boolean asserted negatively: {}",
                                term.type_of()
                            ),
                        };
                    }
                }
            };
            match flatten_to_clauses(&asserted) {
                Some(cs) => clauses.extend(cs),
                None => {
                    // Compound shape not handled by v0.3 alpha CNF flattener.
                    // Fall back to the theory-routing path below for the
                    // sub-set of literals we can route.
                    return self.check_via_theories(&lits);
                }
            }
        }

        // (2) Run the configured SAT backend. With the `cadical`
        //     feature on, route to CaDiCaL; otherwise use the
        //     built-in DPLL (unit propagation + bounded decision
        //     splitting, depth budget 16).
        #[cfg(feature = "cadical")]
        let sat_result = crate::cadical_backend::solve(&clauses);
        #[cfg(not(feature = "cadical"))]
        let sat_result = dpll(&clauses, 16);
        match sat_result {
            BoolResult::Sat => {
                // Propagation found a satisfying assignment; theories
                // may still reject. Route to theories as a second
                // opinion.
                self.check_via_theories(&lits)
            }
            BoolResult::Unsat => SatResult::Unsat { certificate: None },
            BoolResult::Unknown => {
                // Propagation stuck; theories might disagree but
                // can't surface OR-decisions. v0.5 wires in proper
                // decision splitting.
                SatResult::Unknown {
                    reason: "Boolean propagation reached fixpoint with open clauses (decision splitting pending v0.5)".into(),
                }
            }
        }
    }

    /// Legacy path: route raw literals straight to the theory layer.
    /// Used as a fallback when the CNF flattener can't decompose a
    /// compound assertion.
    fn check_via_theories(&mut self, lits: &[(Term, bool)]) -> SatResult {
        self.theories.reset();
        // Strip compound asserts — only send shape-recognizable
        // literals (atom or `(not atom)`) to theories. Anything more
        // complex is opaque to v0.3 theories.
        let mut routable: Vec<(Term, bool)> = Vec::new();
        for (t, p) in lits {
            if t.dest_and().is_some() || t.dest_or().is_some() || t.dest_imp().is_some() {
                continue;
            }
            if let Some(inner) = t.dest_not() {
                routable.push((inner, !p));
            } else {
                routable.push((t.clone(), *p));
            }
        }
        match dpllt::run_once(&mut self.theories, &routable) {
            LoopOutcome::Sat => SatResult::Sat,
            LoopOutcome::Unsat { .. } => SatResult::Unsat { certificate: None },
            LoopOutcome::Unknown { theory, reason } => SatResult::Unknown {
                reason: format!("{theory}: {reason}"),
            },
        }
    }

    /// Expose the flattened literals as classical CNF — useful for
    /// debugging the boundary between Boolean and theory reasoning.
    #[doc(hidden)]
    pub fn debug_clauses(&self) -> Vec<Clause> {
        let lits = self.all_literals();
        let mut clauses = Vec::new();
        for (t, p) in &lits {
            let asserted = if *p { t.clone() }
                else { Term::mk_not(t.clone()).unwrap_or_else(|_| t.clone()) };
            if let Some(cs) = flatten_to_clauses(&asserted) {
                clauses.extend(cs);
            } else {
                clauses.push(vec![Lit::new(t.clone(), *p)]);
            }
        }
        clauses
    }

    pub fn abduce(&mut self, goal: &Term) -> Abductive {
        let engine = SldEngine::new(&self.abducibles);
        let raw = engine.candidates(goal);
        let filtered = self.abduction_state.filter_non_rejected(raw);
        let minimized = minimize(filtered, MinimizePolicy::Standard);
        let ranked = rank_candidates(minimized);
        let candidates = ranked.into_iter().map(|r| r.candidate).collect();
        Abductive { candidates }
    }

    pub fn promote(&mut self, candidate: &adsmt_abduce::sld::Candidate) {
        self.abduction_state.promote(candidate);
    }

    pub fn reject(&mut self, candidate: &adsmt_abduce::sld::Candidate) {
        self.abduction_state.reject(candidate);
    }

    pub fn abduction_state(&self) -> &AbductionState { &self.abduction_state }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_abduce::Abducible;
    use adsmt_core::{Term, Type};

    #[test]
    fn empty_state_is_sat() {
        let mut s = Solver::new();
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn polarity_contradiction_is_unsat() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert_negated(p);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn positive_only_assertions_stay_sat() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(p);
        s.assert(q);
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn push_pop_undoes_contradiction() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.push();
        s.assert_negated(p);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
        s.pop(1);
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn push_pop_preserves_assertions_at_base() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.push();
        let q = Term::var("q", Type::bool_());
        s.assert(q);
        assert_eq!(s.all_literals().len(), 2);
        s.pop(1);
        assert_eq!(s.all_literals().len(), 1);
    }

    #[test]
    fn abduce_returns_candidates_for_registered_abducible() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "x").with_explanation("hint"));
        let r = s.abduce(&p);
        assert_eq!(r.candidates.len(), 1);
    }

    #[test]
    fn promote_persists_hypothesis_across_pop() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "x"));
        s.push();
        let candidates = s.abduce(&p).candidates;
        s.promote(&candidates[0]);
        s.pop(1);
        let after = s.all_literals();
        assert!(after.iter().any(|(t, polarity)| t.alpha_eq(&p) && *polarity));
    }

    #[test]
    fn reject_blocks_future_candidate() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "x"));
        let cands = s.abduce(&p).candidates;
        s.reject(&cands[0]);
        let again = s.abduce(&p).candidates;
        assert!(again.is_empty());
    }

    // === v0.3 Boolean structure tests ===

    #[test]
    fn conjunction_decomposes_to_units() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(Term::mk_and(p, q).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn conjunction_with_contradiction_is_unsat() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let conj = Term::mk_and(p.clone(), Term::mk_not(p).unwrap()).unwrap();
        s.assert(conj);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn implication_modus_ponens() {
        // p, p → q  ⟹  sat (and q forced)
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_imp(p, q).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn implication_modus_tollens_is_unsat() {
        // p, p → q, ¬q  ⟹  unsat
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_imp(p, q.clone()).unwrap());
        s.assert(Term::mk_not(q).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn disjunction_alone_is_sat_via_decision_splitting() {
        // (p ∨ q) alone — DPLL tries p=true → satisfies clause.
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(Term::mk_or(p, q).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn unsat_requiring_branching() {
        // (p ∨ q), (¬p ∨ q), (p ∨ ¬q), (¬p ∨ ¬q) → unsat (needs DPLL)
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(Term::mk_or(p.clone(), q.clone()).unwrap());
        s.assert(Term::mk_or(Term::mk_not(p.clone()).unwrap(), q.clone()).unwrap());
        s.assert(Term::mk_or(p.clone(), Term::mk_not(q.clone()).unwrap()).unwrap());
        s.assert(Term::mk_or(Term::mk_not(p).unwrap(), Term::mk_not(q).unwrap()).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn disjunction_with_unit_premise_propagates() {
        // p, p ∨ q  ⟹  sat (propagation handles it)
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_or(p, q).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn false_assertion_is_immediately_unsat() {
        let mut s = Solver::new();
        s.assert(Term::false_const());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn de_morgan_negated_conjunction() {
        // ¬(p ∧ q) ∧ p ∧ q → unsat
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let conj = Term::mk_and(p.clone(), q.clone()).unwrap();
        s.assert(Term::mk_not(conj).unwrap());
        s.assert(p);
        s.assert(q);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    // === v0.3 theory tests (UF congruence) ===

    #[test]
    fn uf_transitive_equality_over_int_sort() {
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let mut s = Solver::new();
        let a = Term::var("a", int_.clone());
        let b = Term::var("b", int_.clone());
        let c = Term::var("c", int_);
        s.assert(Term::mk_eq(a.clone(), b.clone()).unwrap());
        s.assert(Term::mk_eq(b, c.clone()).unwrap());
        s.assert(Term::mk_not(Term::mk_eq(a, c).unwrap()).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn uf_congruence_under_function_application() {
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let f = Term::const_("f", Type::fun(int_.clone(), int_.clone()).unwrap());
        let mut s = Solver::new();
        let a = Term::var("a", int_.clone());
        let b = Term::var("b", int_);
        let fa = Term::app(f.clone(), a.clone()).unwrap();
        let fb = Term::app(f, b.clone()).unwrap();
        s.assert(Term::mk_eq(a, b).unwrap());
        s.assert(Term::mk_not(Term::mk_eq(fa, fb).unwrap()).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn datatypes_distinct_constructors_is_unsat() {
        use adsmt_core::Kind;
        use adsmt_theory::datatypes::DatatypeDecl;
        let mut s = Solver::new();
        s.declare_datatype(DatatypeDecl::finite_enum(
            "Color",
            vec!["Red".into(), "Green".into(), "Blue".into()],
        ));
        let color = Type::const_("Color", Kind::Type);
        let red = Term::const_("Red", color.clone());
        let green = Term::const_("Green", color);
        s.assert(Term::mk_eq(red, green).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    // === v0.3 quantifier instantiation ===

    #[test]
    fn forall_with_ground_witness_routes_to_uf() {
        // ∀x:Int. P x  ∧  P a is ground witness
        //   ⟹  instantiation gives P a, which is already asserted → sat
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let p = Term::const_("P", Type::fun(int_.clone(), Type::bool_()).unwrap());
        let a = Term::var("a", int_.clone());
        let x = adsmt_core::Var { name: "x".into(), ty: int_.clone() };
        let body = Term::app(p.clone(), Term::Var(std::sync::Arc::new(x.clone()))).unwrap();
        let forall = Term::mk_forall(x, body).unwrap();
        let mut s = Solver::new();
        s.assert(forall);
        s.assert(Term::app(p, a).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn nelson_oppen_uf_to_datatypes() {
        // f a = Red, a = b, f b = Green
        //   ⟹  UF congruence: Red = Green
        //   ⟹  Nelson-Oppen propagation routes the equality to
        //       Datatypes which rejects distinct-constructor.
        use adsmt_core::Kind;
        use adsmt_theory::datatypes::DatatypeDecl;
        let mut s = Solver::new();
        s.declare_datatype(DatatypeDecl::finite_enum(
            "Color",
            vec!["Red".into(), "Green".into(), "Blue".into()],
        ));
        let color = Type::const_("Color", Kind::Type);
        let int_ = Type::const_("Int", Kind::Type);
        let f = Term::const_("f", Type::fun(int_.clone(), color.clone()).unwrap());
        let a = Term::var("a", int_.clone());
        let b = Term::var("b", int_);
        let red = Term::const_("Red", color.clone());
        let green = Term::const_("Green", color);
        s.assert(Term::mk_eq(Term::app(f.clone(), a.clone()).unwrap(), red).unwrap());
        s.assert(Term::mk_eq(a, b.clone()).unwrap());
        s.assert(Term::mk_eq(Term::app(f, b).unwrap(), green).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn forall_combined_with_negation_is_unsat() {
        // ∀x:Int. P x  ∧  ¬(P a)  ⟹  instantiate at a → contradiction.
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let p = Term::const_("P", Type::fun(int_.clone(), Type::bool_()).unwrap());
        let a = Term::var("a", int_.clone());
        let x = adsmt_core::Var { name: "x".into(), ty: int_ };
        let body = Term::app(p.clone(), Term::Var(std::sync::Arc::new(x.clone()))).unwrap();
        let forall = Term::mk_forall(x, body).unwrap();
        let mut s = Solver::new();
        s.assert(forall);
        s.assert(Term::mk_not(Term::app(p, a).unwrap()).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }
}
