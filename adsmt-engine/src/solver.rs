//! Public `Solver` API.

use adsmt_abduce::abducible::AbducibleSet;
use adsmt_abduce::sld::SldEngine;
use adsmt_abduce::workflow::AbductionState;
use adsmt_abduce::{minimize, rank_candidates, MinimizePolicy};
use adsmt_cert::canonical::Sequent;
use adsmt_cert::witness::TheoryWitness;
use adsmt_cert::{CertBuilder, StepBody, StepId};
use adsmt_core::Term;
use adsmt_theory::arrays::Arrays;
use adsmt_theory::bv::Bv;
use adsmt_theory::datatypes::Datatypes;
use adsmt_theory::polite::Combination;
use adsmt_theory::uf::Uf;

#[allow(unused_imports)]
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
        theories.register(Box::new(adsmt_theory::arith::LinArith::lia()));
        theories.register(Box::new(adsmt_theory::arith::LinArith::lra()));
        Self {
            scopes: vec![Scope::new()],
            theories,
            abducibles: AbducibleSet::new(),
            abduction_state: AbductionState::new(),
            cert_builder: CertBuilder::new(),
            // v0.15: default to recording certificates. Callers
            // that don't need them can opt out with
            // `.with_proof_mode(ProofMode::None)` to skip the
            // bookkeeping cost.
            proof_mode: ProofMode::Always,
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
            if let Some(any) = t.as_any_mut()
                && let Some(dt) = any.downcast_mut::<adsmt_theory::datatypes::Datatypes>() {
                    dt.declare(decl);
                    return true;
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

    /// Assert `t` as a positive literal with a source position
    /// (line/column) attached. The position rides through to the
    /// `Assume` cert step's `source_loc` field in the unsat
    /// certificate. Callers without a position should use [`assert`].
    pub fn assert_at(&mut self, t: Term, loc: adsmt_cert::SourceLoc) {
        self.assert_with_polarity_at(t, true, Some(loc));
    }

    /// Like [`assert_negated`] but with a source position.
    pub fn assert_negated_at(&mut self, t: Term, loc: adsmt_cert::SourceLoc) {
        self.assert_with_polarity_at(t, false, Some(loc));
    }

    /// Full-control variant: pick polarity and optionally attach a loc.
    pub fn assert_with_polarity_at(
        &mut self,
        t: Term,
        polarity: bool,
        loc: Option<adsmt_cert::SourceLoc>,
    ) {
        self.scopes
            .last_mut()
            .expect("base scope")
            .assert_at(t, polarity, loc);
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

    /// Attach the known [`SourceLoc`] (from the solver state) to each
    /// `(term, polarity)` in `lits`, returning a parallel
    /// `(term, polarity, loc)` Vec. Locations are looked up by
    /// `(Term, bool)` equality; literals not found in the state map
    /// to `None`, which covers quantifier instantiations and other
    /// solver-internal derivations.
    fn attach_locs(
        &self,
        lits: &[(Term, bool)],
    ) -> Vec<(Term, bool, Option<adsmt_cert::SourceLoc>)> {
        let table = self.all_literals_with_locs();
        lits.iter()
            .map(|(t, p)| {
                let loc = table.iter().find_map(|(tt, pp, l)| {
                    if pp == p && tt == t {
                        *l
                    } else {
                        None
                    }
                });
                (t.clone(), *p, loc)
            })
            .collect()
    }

    /// Like [`all_literals`] but also carries each literal's
    /// optional [`SourceLoc`]. Abductively-accepted hypotheses have
    /// `None` (no parser source position). Used by the unsat-cert
    /// path so each `Assume` step's `:loc` is set when known.
    pub fn all_literals_with_locs(&self) -> Vec<(Term, bool, Option<adsmt_cert::SourceLoc>)> {
        let mut out: Vec<(Term, bool, Option<adsmt_cert::SourceLoc>)> = Vec::new();
        for h in self.abduction_state.accepted() {
            out.push((h.hypothesis.clone(), true, None));
        }
        for sc in &self.scopes {
            for (i, (t, p)) in sc.literals.iter().enumerate() {
                let loc = sc.source_locs.get(i).copied().flatten();
                out.push((t.clone(), *p, loc));
            }
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
                        // Tier 1: Miller-pattern E-matching + bounded
                        // enumeration fallback.
                        for inst in crate::quant::instantiate_one(var, body, &universe) {
                            if !instantiations.iter().any(|t| t.alpha_eq(&inst)) {
                                instantiations.push(inst);
                            }
                        }
                        // Tier 2: conflict-based — pick instantiations
                        // that directly contradict an existing negative
                        // ground assertion.
                        for inst in crate::quant_conflict::conflict_instantiate(var, body, &rest) {
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
        // Tier 4: budget exhausted → abductive escalation. Emit a
        // synthetic candidate per remaining quantifier saying
        // "instantiation needed". The user's `smt_abduce` flow can
        // surface this as a `sorry` hole.
        let lits = self.all_literals();
        let (quants, _) = crate::quant::partition_quantifiers(&lits);
        if !quants.is_empty() {
            let mut candidates: Vec<adsmt_abduce::sld::Candidate> = Vec::new();
            for (var, body) in &quants {
                let formula = Term::mk_forall(var.clone(), body.clone())
                    .unwrap_or_else(|_| body.clone());
                candidates.push(adsmt_abduce::sld::Candidate {
                    hypotheses: vec![formula],
                    explanations: vec![Some(format!(
                        "quantifier `∀{}:{}. {}` needs a witness instantiation \
                         the engine could not synthesize (tier 4 escalation)",
                        var.name, var.ty, body
                    ))],
                    sources: vec!["quant-tier4".into()],
                });
            }
            return SatResult::Abductive { candidates };
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

        // (2) Run the configured SAT backend. Priority order:
        //     `oxiz` (Path A+B default, see oxiz_relationship.md)
        //     > `cadical` (C++ FFI) > built-in DPLL.
        #[cfg(feature = "oxiz")]
        let sat_result = crate::oxiz_backend::solve(&clauses);
        #[cfg(all(feature = "cadical", not(feature = "oxiz")))]
        let sat_result = crate::cadical_backend::solve(&clauses);
        #[cfg(not(any(feature = "oxiz", feature = "cadical")))]
        let sat_result = dpll(&clauses, 16);
        match sat_result {
            BoolResult::Sat => {
                // Propagation found a satisfying assignment; theories
                // may still reject. Route to theories as a second
                // opinion.
                self.check_via_theories(&lits)
            }
            BoolResult::Unsat => {
                let (encoded, drat) = crate::proof_bridge::extract_drat(&clauses);
                // Re-emit the same SAT-level unsat verdict in four
                // byte formats via oxiz crates (P3, v0.15):
                //   - DIMACS DRAT through oxiz-sat (feature `oxiz`)
                //   - Alethe, LFSC, and Coq through oxiz-proof
                //     (feature `oxiz-proof`)
                // When the relevant feature is off the helper
                // returns an empty `Vec` and the cert simply omits
                // that payload.
                let dimacs_bytes = crate::oxiz_drat::emit_via_oxiz_writer(&drat);
                let alethe_bytes = crate::oxiz_proof_emit::emit_alethe_via_oxiz(&encoded);
                let lfsc_bytes = crate::oxiz_proof_emit::emit_lfsc_via_oxiz(&encoded);
                let coq_bytes = crate::oxiz_proof_emit::emit_coq_via_oxiz(&encoded, &drat);
                let witness = TheoryWitness::Drat {
                    clauses: encoded,
                    proof: drat,
                    dimacs_bytes,
                    alethe_bytes,
                    lfsc_bytes,
                    coq_bytes,
                };
                let lits_with_locs = self.attach_locs(&lits);
                let cert = self.build_unsat_cert_opt_with_locs(&lits_with_locs, "SAT", witness);
                SatResult::Unsat { certificate: cert }
            }
            BoolResult::Unknown => {
                SatResult::Unknown {
                    reason: "Boolean propagation reached fixpoint with open clauses (decision splitting pending v0.5)".into(),
                }
            }
        }
    }

    /// Build a [`Certificate`](adsmt_cert::Certificate) for an unsat
    /// verdict. Records every literal in `lits` as an `Assume` step,
    /// then a `Theory` step with the supplied name and witness whose
    /// parents are the assumption ids. Returns the snapshot
    /// certificate; the builder keeps its steps so subsequent calls
    /// can emit incremental deltas (see Q49).
    ///
    /// Returns `None` when [`ProofMode::None`] is set — the engine
    /// then surfaces `SatResult::Unsat { certificate: None }`,
    /// skipping the bookkeeping cost.
    fn build_unsat_cert_opt(
        &mut self,
        lits: &[(Term, bool)],
        theory_name: &str,
        witness: TheoryWitness,
    ) -> Option<adsmt_cert::Certificate> {
        let with_locs: Vec<(Term, bool, Option<adsmt_cert::SourceLoc>)> =
            lits.iter().map(|(t, p)| (t.clone(), *p, None)).collect();
        self.build_unsat_cert_opt_with_locs(&with_locs, theory_name, witness)
    }

    /// Variant of [`build_unsat_cert_opt`] that accepts a per-literal
    /// [`SourceLoc`]. The CLI/parser path supplies positions; the
    /// theory-fallback paths use the `None`-erased variant above.
    fn build_unsat_cert_opt_with_locs(
        &mut self,
        lits: &[(Term, bool, Option<adsmt_cert::SourceLoc>)],
        theory_name: &str,
        witness: TheoryWitness,
    ) -> Option<adsmt_cert::Certificate> {
        if matches!(self.proof_mode, ProofMode::None) {
            return None;
        }
        Some(self.build_unsat_cert_with_locs(lits, theory_name, witness))
    }

    fn build_unsat_cert_with_locs(
        &mut self,
        lits: &[(Term, bool, Option<adsmt_cert::SourceLoc>)],
        theory_name: &str,
        witness: TheoryWitness,
    ) -> adsmt_cert::Certificate {
        let mut assume_ids: Vec<StepId> = Vec::new();
        let mut hyps: Vec<Term> = Vec::new();
        for (t, p, loc) in lits {
            let phi = if *p {
                t.clone()
            } else {
                Term::mk_not(t.clone()).unwrap_or_else(|_| t.clone())
            };
            let id = self.cert_builder.add_with_loc(
                StepBody::Assume(phi.clone()),
                Sequent { hyps: vec![phi.clone()], concl: phi.clone() },
                *loc,
            );
            assume_ids.push(id);
            hyps.push(phi);
        }
        let conclusion = self.cert_builder.add(
            StepBody::Theory {
                name: theory_name.into(),
                witness,
                parents: assume_ids,
            },
            Sequent { hyps, concl: Term::false_const() },
        );
        self.cert_builder.snapshot(conclusion)
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
            LoopOutcome::Unsat { theory, witness } => {
                let cert = self.build_unsat_cert_opt(lits, &theory, witness);
                SatResult::Unsat { certificate: cert }
            }
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

    // === v0.13 cert wiring tests ===

    #[test]
    fn unsat_verdict_carries_certificate() {
        // p ∧ ¬p → unsat with a non-empty Certificate
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        match s.check_sat() {
            SatResult::Unsat { certificate: Some(c) } => {
                // Should have at least the two Assume steps + the
                // Theory closing step.
                assert!(
                    c.steps.len() >= 3,
                    "expected ≥3 cert steps, got {}",
                    c.steps.len(),
                );
                // Final step must be a Theory step.
                let final_step = &c.steps[c.conclusion.0 as usize];
                assert!(matches!(final_step.body, adsmt_cert::StepBody::Theory { .. }));
            }
            other => panic!("expected Unsat with certificate, got {other:?}"),
        }
    }

    #[test]
    fn proof_mode_none_skips_certificate() {
        let mut s = Solver::new().with_proof_mode(ProofMode::None);
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        match s.check_sat() {
            SatResult::Unsat { certificate: None } => {} // expected
            other => panic!("expected Unsat with None cert, got {other:?}"),
        }
    }

    #[test]
    fn proof_mode_always_is_default_after_with_call() {
        let mut s = Solver::new().with_proof_mode(ProofMode::Always);
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        match s.check_sat() {
            SatResult::Unsat { certificate: Some(_) } => {} // expected
            other => panic!("expected Unsat with Some cert, got {other:?}"),
        }
    }

    #[test]
    fn sat_level_unsat_carries_drat_witness() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        match s.check_sat() {
            SatResult::Unsat { certificate: Some(cert) } => {
                let final_step = &cert.steps[cert.conclusion.0 as usize];
                match &final_step.body {
                    adsmt_cert::StepBody::Theory { name, witness, .. } => {
                        assert_eq!(name, "SAT");
                        match witness {
                            adsmt_cert::witness::TheoryWitness::Drat {
                                clauses,
                                proof,
                                dimacs_bytes,
                                alethe_bytes,
                                lfsc_bytes,
                                coq_bytes,
                            } => {
                                assert!(!clauses.is_empty(), "DRAT clauses must include input");
                                assert!(!proof.steps.is_empty(), "DRAT proof must have ≥1 step");
                                // Verify the DRAT proof itself checks out.
                                assert!(
                                    proof.verify(clauses),
                                    "DRAT witness must self-verify"
                                );
                                // Under the `oxiz` feature, the
                                // witness also carries the same
                                // proof as DIMACS DRAT bytes
                                // emitted via oxiz-sat's writer.
                                #[cfg(feature = "oxiz")]
                                {
                                    assert_eq!(
                                        dimacs_bytes, b"0\n",
                                        "oxiz-emitted bytes for the empty-clause proof",
                                    );
                                }
                                #[cfg(not(feature = "oxiz"))]
                                {
                                    assert!(dimacs_bytes.is_empty());
                                }
                                // Under the `oxiz-proof` feature,
                                // Alethe + LFSC byte streams are
                                // produced via oxiz-proof's writers.
                                #[cfg(feature = "oxiz-proof")]
                                {
                                    let alethe = std::str::from_utf8(alethe_bytes).unwrap();
                                    assert!(alethe.contains(":rule resolution"));
                                    let lfsc = std::str::from_utf8(lfsc_bytes).unwrap();
                                    assert!(lfsc.contains("(check"));
                                    let coq = std::str::from_utf8(coq_bytes).unwrap();
                                    assert!(coq.contains("Theorem main_result"));
                                }
                                #[cfg(not(feature = "oxiz-proof"))]
                                {
                                    assert!(alethe_bytes.is_empty());
                                    assert!(lfsc_bytes.is_empty());
                                    assert!(coq_bytes.is_empty());
                                }
                            }
                            other => panic!("expected Drat witness, got {other:?}"),
                        }
                    }
                    _ => panic!("expected Theory step"),
                }
            }
            other => panic!("expected Unsat with cert, got {other:?}"),
        }
    }

    #[test]
    fn unsat_certificate_emits_to_sexpr() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        match s.check_sat() {
            SatResult::Unsat { certificate: Some(cert) } => {
                let out = adsmt_cert::emit_certificate(&cert);
                assert!(out.starts_with("(proof"));
                assert!(out.contains("(assume "));
                assert!(out.contains("(theory :name"));
                assert!(out.contains("(conclude "));
            }
            other => panic!("expected Unsat with cert, got {other:?}"),
        }
    }

    #[test]
    fn assert_at_threads_source_loc_into_cert_assume_step() {
        use adsmt_cert::{SourceLoc, StepBody};
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert_at(p.clone(), SourceLoc::new(3, 8));
        s.assert_negated_at(p, SourceLoc::new(4, 12));
        let SatResult::Unsat {
            certificate: Some(cert),
        } = s.check_sat()
        else {
            panic!("expected Unsat with cert");
        };
        // Find the two Assume steps and check their locs match what
        // we passed in via assert_at / assert_negated_at.
        let mut found = std::collections::HashSet::new();
        for step in &cert.steps {
            if matches!(step.body, StepBody::Assume(_)) {
                if let Some(loc) = step.source_loc {
                    found.insert((loc.line, loc.column));
                }
            }
        }
        assert!(found.contains(&(3, 8)), "assume @ (3,8) missing in {found:?}");
        assert!(found.contains(&(4, 12)), "assume @ (4,12) missing in {found:?}");
        // Emit must surface :loc attribute in S-expr form.
        let out = adsmt_cert::emit_certificate(&cert);
        assert!(out.contains(":loc 3:8"));
        assert!(out.contains(":loc 4:12"));
    }

    #[test]
    fn plain_assert_keeps_source_loc_none() {
        use adsmt_cert::StepBody;
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        let SatResult::Unsat {
            certificate: Some(cert),
        } = s.check_sat()
        else {
            panic!("expected Unsat with cert");
        };
        for step in &cert.steps {
            if matches!(step.body, StepBody::Assume(_)) {
                assert!(step.source_loc.is_none());
            }
        }
    }

    #[test]
    fn cert_records_theory_name_for_theory_unsat() {
        // (= a b), (= b c), (not (= a c)) — UF congruence closure
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let mut s = Solver::new();
        let a = Term::var("a", int_.clone());
        let b = Term::var("b", int_.clone());
        let c = Term::var("c", int_);
        s.assert(Term::mk_eq(a.clone(), b.clone()).unwrap());
        s.assert(Term::mk_eq(b, c.clone()).unwrap());
        s.assert(Term::mk_not(Term::mk_eq(a, c).unwrap()).unwrap());
        match s.check_sat() {
            SatResult::Unsat { certificate: Some(cert) } => {
                // Find the final Theory step and check its name.
                let last = &cert.steps[cert.conclusion.0 as usize];
                match &last.body {
                    adsmt_cert::StepBody::Theory { name, .. } => {
                        // Could be "UF" or "polite" depending on which
                        // theory surfaced the conflict first.
                        assert!(
                            name == "UF" || name == "polite",
                            "unexpected theory name in cert: {name}"
                        );
                    }
                    other => panic!("expected Theory step, got {other:?}"),
                }
            }
            other => panic!("expected Unsat with cert, got {other:?}"),
        }
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
