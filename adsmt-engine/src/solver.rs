//! Public `Solver` API.

use std::collections::HashMap;

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
use crate::bool_solver::{dpll, dpll_with_restarts, BoolResult};
#[allow(unused_imports)]
use crate::cdcl::cdcl_with_restarts;
use crate::cnf::{flatten_to_clauses, Clause, Lit};
use crate::dpllt::{self, LoopOutcome};
use crate::result::{Abductive, SatResult};
use crate::state::Scope;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ProofMode { None, Always }

/// Outcome of [`Solver::replay_aot_cdcl_trace`] — the §3.5.F
/// guard-evaluation gate.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ReplayOutcome {
    /// At least one of the trace's guards no longer holds
    /// against the current engine state; the caller should
    /// fall through to the regular `check_sat_with_deadline`
    /// path.  v0 uses the agreed "full discard on miss"
    /// semantic from the §3.5 counter-ack §5.4 — partial-replay
    /// fallback is the v1 follow-up that consumes
    /// `CdclTrace::checkpoints`.
    GuardMiss,
    /// Every guard held.  v0: the caller has informed the
    /// gate that the trace's algebraic signature is still
    /// alive in the current query's ideal.  Once §3.5.F is
    /// promoted from skeleton to full replay, this variant
    /// returns the trace's verdict; for now the caller still
    /// falls through to full CDCL because the engine-side
    /// event-replay machinery is the §3.5.F follow-up.
    GuardsPassed,
}

// `adsmt_jit` is the §3.2 / §3.5.D companion crate; `Solver::
// replay_aot_cdcl_trace` borrows its `CdclTrace` / `JitGuard` /
// `check_guard` machinery so the replay path and the recorder
// share one vocabulary (per the §3.5 counter-ack §5.5
// vocabulary-reuse).  No `use` needed — the dep entry in
// Cargo.toml brings the crate into scope; call sites name
// the type via `adsmt_jit::...`.

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
        // Default theory roster: UF, Datatypes, Arrays, BV, and
        // LinArith (LIA + LRA). LinArith uses the v0.13 Simplex
        // tableau (`adsmt-theory/src/arith_simplex.rs`).
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

    /// Register the §3.4 GF(2) Gröbner-basis theory plugin per the
    /// verus-fork engine-refactor request (`§3.4` of
    /// `.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`).
    ///
    /// The plugin sits in `Combination::register` alongside the
    /// other theories.  Its behaviour is governed by the
    /// [`adsmt_theory_finite_field::FiniteFieldConfig`] knobs:
    ///
    /// - `periodic_interval: usize` (default `0` = disabled) —
    ///   runs one F4 pass every `N`-th call to the theory's
    ///   `check`; a `1 ∈ basis` verdict surfaces as
    ///   `CheckResult::Unsat` and the engine short-circuits with
    ///   the FiniteField `TheoryWitness`.
    /// - `try_at_budget_exhaustion: bool` (default `false`) —
    ///   when `check_sat_with_deadline` is about to return
    ///   `Unknown` the engine first calls
    ///   `FiniteFieldTheory::force_check`; an UNSAT verdict
    ///   replaces the `Unknown` with a real `Unsat` carrying an
    ///   empty `core` (a structured `core` populated from the
    ///   basis is a v1.x follow-up).
    ///
    /// **Scope caveat**: the plugin only sees the CNF flattened
    /// from the user's top-level assertions, *not* quantifier
    /// instantiations or learnt clauses produced inside the
    /// DPLL(T) loop.  If a UNSAT proof requires those, the
    /// plugin's F4 pass cannot certify it — but it also cannot
    /// claim a spurious UNSAT.  In practice this is the right
    /// trade-off for the verus-fork bit-vector queries §3.4
    /// targets (mask invariants, overflow guards, witnessed AEAD
    /// lemmas), which reduce to propositional `GF(2)` ideals
    /// directly from the top-level CNF.
    ///
    /// Builder-pattern style:
    /// `Solver::default().with_finite_field(config)`.
    pub fn with_finite_field(
        mut self,
        config: adsmt_theory_finite_field::FiniteFieldConfig,
    ) -> Self {
        let theory = adsmt_theory_finite_field::FiniteFieldTheory::new(config);
        self.theories.register(Box::new(theory));
        self
    }

    /// Pre-assert every term in a reconstructed `.luart` prelude
    /// bank (§3.1.D — the load half of the §3.1 AOT pipeline).
    /// Routes each prelude term through `intern_external` so its
    /// `Arc<TermInner>` identity merges with anything per-query
    /// input rebuilds structurally, then funnels through the
    /// regular `assert_at` path so the cert ledger records each
    /// prelude axiom with a synthetic `(line=0, col=<index>)`
    /// source location.  The optional per-axiom `qid` carried in
    /// the prelude is currently ignored — §3.2's JIT-guard
    /// metadata is the natural consumer; v0 keeps the wire field
    /// available without yet routing it into the engine.
    ///
    /// Builder-pattern style:
    /// `Solver::default().with_aot_prelude(prelude)`.
    pub fn with_aot_prelude(mut self, prelude: adsmt_aot::ReconstructedPrelude) -> Self {
        for (idx, (term, _qid)) in prelude.assertions.into_iter().enumerate() {
            let canonical = adsmt_aot::intern_external(&term);
            let loc = adsmt_cert::SourceLoc::new(0, idx as u32);
            self.assert_at(canonical, loc);
        }
        self
    }

    /// §3.5.C entry point — consume a
    /// [`adsmt_aot::ReconstructedCdclPrelude`] (Term-DAG +
    /// optional CDCL scope-0 snapshot from the v1 `.luart-cdcl`
    /// artefact).
    ///
    /// v0 semantics: the prelude assertions thread through
    /// [`Self::with_aot_prelude`] exactly as before; the CDCL
    /// section is stashed away for the §3.5.F replay-or-fallback
    /// dispatcher (which lands in a follow-up patch on the
    /// `check_sat_with_deadline` path).  The skeleton currently
    /// drops the section because the engine's CDCL state is not
    /// yet exposed for external restoration — once §3.5.F wires
    /// `restore_cdcl_state(...)`, the bytes recovered here become
    /// the head-start the per-query solve inherits.
    ///
    /// Surfacing the builder now (v0 = behaves like
    /// `with_aot_prelude`) lets `lu-smt --aot-load` exercise the
    /// new artefact shape end-to-end without coupling the CLI
    /// landing to the engine-side state-restoration work.
    pub fn with_aot_cdcl(
        self,
        prelude: adsmt_aot::ReconstructedCdclPrelude,
    ) -> Self {
        let _cdcl_section_for_3_5_f = prelude.cdcl_section;
        self.with_aot_prelude(prelude.prelude)
    }

    /// §3.5.F replay dispatcher (v0 skeleton).  Evaluates every
    /// guard in `trace.guards` + the end-of-trace
    /// [`GF2Snapshot`]-derived basis against the current
    /// engine state.  Returns [`ReplayOutcome::GuardMiss`] on
    /// the first guard failure (matching the v0 "full discard
    /// on miss" semantics agreed in the §3.5 counter-ack §5.4 —
    /// partial-replay fallback via mid-trace checkpoints is the
    /// v1 follow-up); returns
    /// [`ReplayOutcome::GuardsPassed`] when every guard holds.
    ///
    /// v0 does not yet replay the recorded events through the
    /// CDCL state machine — that wiring lands once the engine
    /// side exposes the `restore_cdcl_state` helper the trace's
    /// events feed into.  Calling this method is therefore a
    /// guard-evaluation gate only; the caller (lu-smt
    /// `(check-sat)` dispatcher in the §3.5.G CLI surface)
    /// uses the result to decide between "try the trace" and
    /// "fall through to full CDCL".
    pub fn replay_aot_cdcl_trace(
        &self,
        trace: &adsmt_jit::CdclTrace,
        classes: &[(String, u32)],
    ) -> ReplayOutcome {
        // Skeleton-shape guards use the live formula's
        // depth-3 hash; with no formula in scope (the trace
        // doesn't carry its own), pass through `SkeletonShape(0)`
        // and let the caller seed a real hash before the v1
        // dispatcher.
        let live_skeleton = adsmt_jit::trace::SkeletonShape(0);
        for guard in &trace.guards {
            let pass = adsmt_jit::check_guard(
                guard,
                &trace.signature.basis,
                classes,
                live_skeleton,
            );
            if pass == adsmt_jit::guard::GuardResult::Fail {
                return ReplayOutcome::GuardMiss;
            }
        }
        ReplayOutcome::GuardsPassed
    }

    /// `true` iff the GF(2) Gröbner theory plugin has been
    /// registered via [`Self::with_finite_field`].  Internal
    /// helper for the engine hooks below; downstream code that
    /// cares about the plugin's configuration should instead poke
    /// at it directly through [`Self::finite_field_mut`].
    fn has_finite_field(&self) -> bool {
        self.theories
            .theories()
            .iter()
            .any(|t| t.name() == "FiniteField")
    }

    /// Mutable handle to the registered
    /// [`adsmt_theory_finite_field::FiniteFieldTheory`], if any.
    /// Used by the budget-exhaustion + clause-install hooks
    /// inside `check_sat_with_deadline` and exposed publicly so
    /// callers can re-tune the configuration mid-session.
    pub fn finite_field_mut(
        &mut self,
    ) -> Option<&mut adsmt_theory_finite_field::FiniteFieldTheory> {
        for t in self.theories.theories_mut() {
            if t.name() != "FiniteField" {
                continue;
            }
            if let Some(any) = t.as_any_mut()
                && let Some(ff) = any
                    .downcast_mut::<adsmt_theory_finite_field::FiniteFieldTheory>(
                )
            {
                return Some(ff);
            }
        }
        None
    }

    /// Translate the engine's current CNF clause set into the
    /// DIMACS shape the standalone GF(2) decider consumes and
    /// install it on the registered FiniteField plugin.  Called by
    /// `check_sat_with_deadline` at the top of every `check_sat`
    /// so the plugin's `force_check` / periodic pass always sees
    /// the live clause set.  Assertions that `flatten_to_clauses`
    /// returns `None` for (non-Bool top-level terms — equalities,
    /// theory-shaped literals, etc.) are conservatively skipped;
    /// the GF(2) decider only reasons about the propositional
    /// fragment, so missing those rows is sound (it can only
    /// under-approximate UNSAT, never claim spurious UNSAT).
    fn install_finite_field_clauses(&mut self) {
        if !self.has_finite_field() {
            return;
        }
        let mut all_clauses: Vec<crate::cnf::Clause> = Vec::new();
        for term in self.all_assertions() {
            if let Some(mut cs) = crate::cnf::flatten_to_clauses(&term) {
                all_clauses.append(&mut cs);
            }
        }
        use std::collections::HashMap;
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut next_var: u32 = 1;
        let dimacs: Vec<Vec<i32>> = all_clauses
            .iter()
            .map(|c| {
                c.iter()
                    .map(|lit| {
                        let key = lit.atom.to_string();
                        let id = *var_map.entry(key).or_insert_with(|| {
                            let v = next_var;
                            next_var += 1;
                            v
                        });
                        if lit.polarity {
                            id as i32
                        } else {
                            -(id as i32)
                        }
                    })
                    .collect()
            })
            .collect();
        let n_vars = next_var - 1;
        if let Some(ff) = self.finite_field_mut() {
            ff.install_dimacs_clauses(dimacs, n_vars);
        }
    }

    /// Last-resort GF(2) Gröbner check.  Returns `Some(witness)`
    /// when `try_at_budget_exhaustion` is on and the F4 pass
    /// finds `1 ∈ basis`.  Otherwise `None`.
    fn try_finite_field_at_budget_exhaustion(
        &mut self,
    ) -> Option<adsmt_cert::witness::TheoryWitness> {
        let ff = self.finite_field_mut()?;
        if !ff.config().try_at_budget_exhaustion {
            return None;
        }
        ff.force_check()
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

    /// Assert `t` with explicit polarity. Routes through
    /// [`Self::assert_with_polarity_at`] so the NNF + Skolemization
    /// pre-pass fires for quantified asserts regardless of whether
    /// the caller supplied a source location.
    pub fn assert_with_polarity(&mut self, t: Term, polarity: bool) {
        self.assert_with_polarity_at(t, polarity, None);
    }

    /// Assert `t` as a positive literal with a source position
    /// (line/column) attached. The position rides through to the
    /// `Assume` cert step's `source_loc` field in the unsat
    /// certificate. Callers without a position should use [`assert`].
    pub fn assert_at(&mut self, t: Term, loc: adsmt_cert::SourceLoc) {
        self.assert_with_polarity_at(t, true, Some(loc));
    }

    /// Like [`Self::assert_negated`] but with a source position.
    pub fn assert_negated_at(&mut self, t: Term, loc: adsmt_cert::SourceLoc) {
        self.assert_with_polarity_at(t, false, Some(loc));
    }

    /// Full-control variant: pick polarity and optionally attach a loc.
    ///
    /// Quantified asserts are first oriented (the polarity is folded
    /// into the term via `not`) and then passed through
    /// [`adsmt_quant::normalize_for_engine`] for NNF + Skolemization,
    /// so the rest of the pipeline (`partition_quantifiers`,
    /// E-matching, theory layer) only ever sees positive
    /// `forall`s and ground formulas. Pure-propositional asserts
    /// short-circuit the rewrite and keep their original Term shape
    /// — useful for the cert and for tests that pattern-match the
    /// asserted form.
    pub fn assert_with_polarity_at(
        &mut self,
        t: Term,
        polarity: bool,
        loc: Option<adsmt_cert::SourceLoc>,
    ) {
        let (final_term, final_polarity) =
            if adsmt_quant::skolemize::contains_quantifier(&t) {
                let oriented = if polarity {
                    t
                } else {
                    Term::mk_not(t).expect("Bool")
                };
                (adsmt_quant::normalize_for_engine(&oriented), true)
            } else {
                (t, polarity)
            };
        self.scopes
            .last_mut()
            .expect("base scope")
            .assert_at(final_term, final_polarity, loc);
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

    /// Like [`Self::all_literals`] but also carries each literal's
    /// optional [`SourceLoc`](adsmt_cert::SourceLoc). Abductively-accepted hypotheses have
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
        self.check_sat_with_deadline(None)
    }

    /// `check_sat` with an optional wall-clock deadline.  Callers
    /// translate `(set-option :rlimit N)` / `(set-option :timeout N)`
    /// from SMT-LIB into an absolute `Instant` here; the engine
    /// short-circuits the Tier-1/2/3 instantiation loop the moment
    /// `Instant::now() >= deadline` and returns Unknown with
    /// `:reason-unknown "rlimit exceeded"` — the same outcome a Z3
    /// `:rlimit` exhaustion produces.  `None` reverts to the
    /// previous unbounded behaviour.
    pub fn check_sat_with_deadline(
        &mut self,
        deadline: Option<std::time::Instant>,
    ) -> SatResult {
        // §3.4 hook: install the live CNF clause set into the
        // GF(2) Gröbner theory plugin (if registered via
        // `with_finite_field`) so its periodic-interval pass and
        // budget-exhaustion `force_check` both see the up-to-date
        // formula.  No-op when the plugin isn't registered.
        self.install_finite_field_clauses();

        let original_result = self.check_sat_inner(deadline);

        // §3.4 budget-exhaustion hook: if CDCL+Tier-1/2/3 ran out
        // of time and the registered FiniteField plugin has
        // `try_at_budget_exhaustion = true`, give the GF(2) basis
        // one final shot.  An `1 ∈ basis` certificate replaces
        // the Unknown verdict with a real Unsat carrying the
        // FiniteField `TheoryWitness`.
        if let SatResult::Unknown { .. } = &original_result
            && self.try_finite_field_at_budget_exhaustion().is_some()
        {
            let core =
                crate::result::UnsatCore::from_assertions(&self.all_assertions());
            return SatResult::Unsat { certificate: None, core };
        }
        original_result
    }

    /// The original `check_sat` body extracted so the §3.4 hooks
    /// can wrap it without complicating the body's already busy
    /// closure-capture environment.
    fn check_sat_inner(
        &mut self,
        deadline: Option<std::time::Instant>,
    ) -> SatResult {
        const QUANTIFIER_ROUNDS: usize = 3;

        // Closure capturing the deadline for compact early-exit
        // sites inside the instantiation loop.
        let expired = |d: Option<std::time::Instant>| -> bool {
            d.is_some_and(|dl| std::time::Instant::now() >= dl)
        };

        // v0.3 quantifier loop: at each round, partition asserted
        // formulas into quantifiers and ground, then run the ground
        // solver. If Sat, run a Miller-pattern E-matching pass and
        // add fresh instantiations as ground assertions; loop again
        // until either fixpoint or the round budget is exhausted.
        let mut instantiations: Vec<Term> = Vec::new();
        for _round in 0..QUANTIFIER_ROUNDS {
            if expired(deadline) {
                return SatResult::Unknown {
                    reason: "rlimit exceeded".to_string(),
                };
            }
            let mut combined = self.all_literals();
            for inst in &instantiations {
                combined.push((inst.clone(), true));
            }
            let outcome = self.check_ground_with_deadline(&combined, deadline);
            match outcome {
                SatResult::Sat { model: ground_model } => {
                    // Try quantifier instantiation; if no new
                    // instances, we're done at Sat.
                    let (quants, rest) = crate::quant::partition_quantifiers(&combined);
                    if quants.is_empty() {
                        return SatResult::Sat {
                            model: ground_model,
                        };
                    }
                    let universe = crate::quant::collect_universe(&rest);
                    let prev = instantiations.len();
                    for (var, body) in &quants {
                        if expired(deadline) {
                            return SatResult::Unknown {
                                reason: "rlimit exceeded".to_string(),
                            };
                        }
                        let before_tier1 = instantiations.len();
                        // Tier 1: Miller-pattern E-matching.
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
                        // Tier 3: bounded enumeration. Fires only when
                        // Tier 1 and Tier 2 produced nothing new for
                        // this quantifier — keeps universe-wide blowup
                        // off the hot path.
                        if instantiations.len() == before_tier1 {
                            for inst in adsmt_quant::enumerate::enumerate(
                                var,
                                body,
                                &universe,
                                adsmt_quant::enumerate::DEFAULT_TIER3_BUDGET,
                            ) {
                                if expired(deadline) {
                                    return SatResult::Unknown {
                                        reason: "rlimit exceeded".to_string(),
                                    };
                                }
                                if !instantiations.iter().any(|t| t.alpha_eq(&inst)) {
                                    instantiations.push(inst);
                                }
                            }
                        }
                    }
                    if instantiations.len() == prev {
                        return SatResult::Sat {
                            model: ground_model,
                        };
                    }
                    // else loop with the extended assertion set
                }
                other => return other,
            }
        }
        // Tier 4 (v0.19 D.1): budget exhausted → abductive escalation,
        // now run through `minimize` + `rank_candidates` before
        // returning. The minimisation step drops candidates that are
        // strictly subsumed by another remaining quantifier (so
        // duplicated `∀x. P x` assertions don't emit two `sorry`
        // suggestions) and the ranking step orders the survivors by
        // hypothesis-count then by depth so the UI can surface the
        // most actionable candidate first.
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
            let minimized = minimize(candidates, MinimizePolicy::Standard);
            let ranked = rank_candidates(minimized);
            return SatResult::Abductive { candidates: ranked };
        }
        SatResult::Unknown {
            reason: format!("quantifier instantiation budget ({QUANTIFIER_ROUNDS} rounds) exhausted"),
        }
    }

    /// Ground (quantifier-free) reasoning over the given literals.
    /// Internal helper kept for symmetry with the deadline-aware
    /// variant; currently every internal call site already has a
    /// deadline to thread (the unbounded path simply passes `None`
    /// to `check_ground_with_deadline` directly), so this thin
    /// wrapper sees no in-tree use yet.  Kept reachable for
    /// downstream tests and for future Tier-4 escalation paths
    /// that may want the unbounded shape; the dead-code lint is
    /// silenced accordingly.
    #[allow(dead_code)]
    fn check_ground(&mut self, lits: &[(Term, bool)]) -> SatResult {
        self.check_ground_with_deadline(lits, None)
    }

    /// Deadline-aware variant of [`Self::check_ground`].  Threads
    /// the wall-clock budget into the CDCL restart loop and checks
    /// it once more before the (potentially expensive) theory-check
    /// fallback fires.  Returns Unknown with `:reason-unknown
    /// "rlimit exceeded"` whenever the deadline lapses inside the
    /// ground path.
    fn check_ground_with_deadline(
        &mut self,
        lits: &[(Term, bool)],
        deadline: Option<std::time::Instant>,
    ) -> SatResult {
        let expired = |d: Option<std::time::Instant>| -> bool {
            d.is_some_and(|dl| std::time::Instant::now() >= dl)
        };
        if expired(deadline) {
            return SatResult::Unknown {
                reason: "rlimit exceeded".to_string(),
            };
        }
        // Strip quantifier asserts from the ground path — they're
        // handled by the surrounding instantiation loop.
        let (_quants, lits): (Vec<_>, Vec<_>) = lits
            .iter()
            .cloned()
            .partition(|(t, p)| *p && t.dest_forall().is_some());
        // (1) Decompose every asserted (term, polarity) into CNF clauses.
        let mut clauses: Vec<Clause> = Vec::new();
        for (term, polarity) in &lits {
            if expired(deadline) {
                return SatResult::Unknown {
                    reason: "rlimit exceeded".to_string(),
                };
            }
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
            match crate::cnf::flatten_to_clauses_with_deadline(&asserted, deadline) {
                Some(cs) => clauses.extend(cs),
                None => {
                    if expired(deadline) {
                        return SatResult::Unknown {
                            reason: "rlimit exceeded".to_string(),
                        };
                    }
                    // Compound shape not handled by v0.3 alpha CNF flattener.
                    // Fall back to the theory-routing path below for the
                    // sub-set of literals we can route.
                    return self.check_via_theories(&lits);
                }
            }
        }
        if expired(deadline) {
            return SatResult::Unknown {
                reason: "rlimit exceeded".to_string(),
            };
        }

        // (2) Run the configured SAT backend. Priority order:
        //     `oxiz` (Path A+B default, see oxiz_relationship.md)
        //     > `cadical` (C++ FFI) > built-in CDCL.
        //
        // v0.19 B.1 wrapped the legacy DPLL fallback in Luby
        // restarts. v0.21 B.1 replaces that path with the full
        // CDCL solver (`adsmt-engine::cdcl::cdcl_with_restarts`)
        // — trail + 1-UIP + learnt clauses + non-chronological
        // backjump + Luby restarts + VSIDS. `base_conflicts=64`
        // × `restarts=12` covers the canonical 1,1,2,1,1,2,4,…
        // schedule scaled into 64 / 64 / 128 / 64 / 64 / 128 /
        // 256 / … conflict budgets, which is enough to close all
        // 76 workspace-level tests without measurable
        // easy-case regression.
        #[cfg(feature = "oxiz")]
        let sat_result = crate::oxiz_backend::solve(&clauses);
        #[cfg(all(feature = "cadical", not(feature = "oxiz")))]
        let sat_result = crate::cadical_backend::solve(&clauses);
        #[cfg(not(any(feature = "oxiz", feature = "cadical")))]
        let sat_result =
            crate::cdcl::cdcl_with_restarts_deadline(&clauses, 64, 12, deadline);
        match sat_result {
            BoolResult::Sat => {
                // The model-extracting re-run must carry the same
                // wall-clock deadline as the first CDCL call.
                // Otherwise a large prelude (verus emits 1000+
                // assertions before the first `(check-sat)`) can
                // burn the entire `:rlimit` budget on the
                // satisfiability check, leave nothing for the
                // model-carrying re-run, and then hang forever
                // here while ostensibly under a tight rlimit.
                let model = match crate::cdcl::cdcl_with_restarts_with_model_deadline(
                    &clauses,
                    64,
                    12,
                    deadline,
                ) {
                    crate::cdcl::CdclOutcome::Sat { model } => model,
                    _ => HashMap::new(),
                };
                if expired(deadline) {
                    return SatResult::Unknown {
                        reason: "rlimit exceeded".to_string(),
                    };
                }
                self.check_via_theories_with_model(&lits, model)
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
                let core = crate::result::UnsatCore::from_assertions(&self.all_assertions());
                SatResult::Unsat {
                    certificate: cert,
                    core,
                }
            }
            BoolResult::Unknown => {
                SatResult::Unknown {
                    reason: "SAT backend returned Unknown (oxiz-sat / CaDiCaL gave up; rare path)".into(),
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
    /// then surfaces `SatResult::Unsat { certificate: None, .. }`,
    /// skipping the bookkeeping cost.
    /// Build the unsat certificate with per-literal source locs
    /// attached. Both the SAT-level unsat path
    /// (`build_unsat_cert_opt_with_locs` called from
    /// [`check_ground`]) and the theory-unsat path (called from
    /// [`check_via_theories`]) feed positions through
    /// [`attach_locs`], so every `Assume` step that traces back to
    /// a parser-supplied `assert_at` carries a `:loc` annotation.
    ///
    /// Returns `None` when [`ProofMode::None`] is set — the engine
    /// then surfaces `SatResult::Unsat { certificate: None, .. }`,
    /// skipping the bookkeeping cost.
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
        self.check_via_theories_with_model(lits, HashMap::new())
    }

    /// Variant of [`Self::check_via_theories`] that threads the
    /// boolean assignment from the SAT layer through to the
    /// verdict's `SatResult::Sat::model`.
    fn check_via_theories_with_model(
        &mut self,
        lits: &[(Term, bool)],
        bool_assignment: HashMap<String, bool>,
    ) -> SatResult {
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
            LoopOutcome::Sat => SatResult::Sat {
                model: crate::result::Model::from_assignment(bool_assignment),
            },
            LoopOutcome::Unsat { theory, witness } => {
                // Cross-reference each `lits` entry against the
                // solver-state literal table to recover the
                // source position recorded by `assert_at` at the
                // CLI boundary. Theory unsat now threads `:loc`
                // through the cert exactly like the SAT-level
                // unsat path.
                let lits_with_locs = self.attach_locs(lits);
                let cert = self.build_unsat_cert_opt_with_locs(
                    &lits_with_locs,
                    &theory,
                    witness,
                );
                let core = crate::result::UnsatCore::from_assertions(&self.all_assertions());
                SatResult::Unsat {
                    certificate: cert,
                    core,
                }
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
        Abductive { candidates: ranked }
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
        s.promote(&candidates[0].candidate);
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
        s.reject(&cands[0].candidate);
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
            SatResult::Unsat { certificate: Some(c), .. } => {
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
            SatResult::Unsat { certificate: None, .. } => {} // expected
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
            SatResult::Unsat { certificate: Some(_), .. } => {} // expected
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
            SatResult::Unsat { certificate: Some(cert), .. } => {
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
            SatResult::Unsat { certificate: Some(cert), .. } => {
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
        let SatResult::Unsat { certificate: Some(cert), .. } = s.check_sat()
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
        let SatResult::Unsat { certificate: Some(cert), .. } = s.check_sat()
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
            SatResult::Unsat { certificate: Some(cert), .. } => {
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
    fn theory_unsat_path_threads_source_loc_into_assume_steps() {
        // UF congruence — falls through to `check_via_theories`
        // because the CNF flattener sees only flat equalities.
        // Each `assert_at` position must arrive at the
        // corresponding `Assume` cert step's `source_loc`.
        use adsmt_cert::{SourceLoc, StepBody};
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let mut s = Solver::new();
        let a = Term::var("a", int_.clone());
        let b = Term::var("b", int_.clone());
        let c = Term::var("c", int_);
        s.assert_at(
            Term::mk_eq(a.clone(), b.clone()).unwrap(),
            SourceLoc::new(10, 1),
        );
        s.assert_at(
            Term::mk_eq(b, c.clone()).unwrap(),
            SourceLoc::new(11, 1),
        );
        s.assert_negated_at(
            Term::mk_eq(a, c).unwrap(),
            SourceLoc::new(12, 1),
        );
        let SatResult::Unsat { certificate: Some(cert), .. } = s.check_sat()
        else {
            panic!("expected Unsat with cert");
        };
        let mut found: std::collections::HashSet<(u32, u32)> =
            std::collections::HashSet::new();
        for step in &cert.steps {
            if matches!(step.body, StepBody::Assume(_)) {
                if let Some(loc) = step.source_loc {
                    found.insert((loc.line, loc.column));
                }
            }
        }
        assert!(found.contains(&(10, 1)), "assume @ (10,1) missing in {found:?}");
        assert!(found.contains(&(11, 1)), "assume @ (11,1) missing in {found:?}");
        assert!(found.contains(&(12, 1)), "assume @ (12,1) missing in {found:?}");
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
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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

    // === NNF + Skolemization pre-assert pipeline ===

    fn unary_pred(name: &str, dom: Type) -> Term {
        // Mirror the lu-smt CLI convention: declared predicates are
        // `Term::var` (so congruence closure can carry their
        // equalities), not `Term::const_`.
        Term::var(name, Type::fun(dom, Type::bool_()).unwrap())
    }

    #[test]
    fn negated_exists_via_nnf_is_unsat() {
        // P a  ∧  ¬∃x:Int. P x   normalises to
        // P a  ∧   ∀x:Int. ¬P x  which instantiates at a → ⊥.
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let p = unary_pred("P", int_.clone());
        let a = Term::var("a", int_.clone());
        let x = adsmt_core::Var { name: "x".into(), ty: int_ };
        let body = Term::app(p.clone(), Term::Var(std::sync::Arc::new(x.clone()))).unwrap();
        let exists = Term::mk_exists(x, body).unwrap();
        let mut s = Solver::new();
        s.assert(Term::app(p, a).unwrap());
        s.assert(Term::mk_not(exists).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn top_level_existential_is_skolemized_to_sat() {
        // ∃x:Int. P x  on its own is satisfiable — Skolemization
        // replaces x with a fresh constant and the engine accepts the
        // resulting ground assertion.
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let p = unary_pred("P", int_.clone());
        let x = adsmt_core::Var { name: "x".into(), ty: int_ };
        let body = Term::app(p, Term::Var(std::sync::Arc::new(x.clone()))).unwrap();
        let exists = Term::mk_exists(x, body).unwrap();
        let mut s = Solver::new();
        s.assert(exists);
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
    }

    #[test]
    fn negated_forall_via_skolem_is_unsat() {
        // ∀x:Int. P x   ∧   ¬∀x:Int. P x    — the negated forall
        // becomes ∃x. ¬P x, which Skolemizes to ¬P(c) for a fresh c,
        // and the universal instantiates at c → contradiction.
        use adsmt_core::Kind;
        let int_ = Type::const_("Int", Kind::Type);
        let p = unary_pred("P", int_.clone());
        let x = adsmt_core::Var { name: "x".into(), ty: int_ };
        let body = Term::app(p, Term::Var(std::sync::Arc::new(x.clone()))).unwrap();
        let forall = Term::mk_forall(x, body).unwrap();
        let mut s = Solver::new();
        s.assert(forall.clone());
        s.assert(Term::mk_not(forall).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    // === v0.19 D.1 — Tier 4 escalation goes through minimize + rank ===

    #[test]
    fn tier4_minimize_rank_pipeline_subsumes_strictly_smaller_candidate() {
        // Pin the post-minimize-rank shape that D.1 wires into Tier
        // 4: a strictly-smaller candidate subsumes a strictly-larger
        // one, and rank preserves the survivor. The solver-side path
        // emitting these candidates fires when the quant
        // instantiation loop exhausts its budget — covered by the
        // forall integration tests above.
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let small = adsmt_abduce::sld::Candidate {
            hypotheses: vec![p.clone()],
            explanations: vec![Some("tier4 escalation: needs p".into())],
            sources: vec!["quant-tier4".into()],
        };
        let big = adsmt_abduce::sld::Candidate {
            hypotheses: vec![p, q],
            explanations: vec![
                Some("tier4 escalation: needs p".into()),
                Some("tier4 escalation: needs q".into()),
            ],
            sources: vec!["quant-tier4".into(), "quant-tier4".into()],
        };
        let minimized = minimize(vec![big, small], MinimizePolicy::Standard);
        assert_eq!(minimized.len(), 1, "smaller candidate subsumes bigger");
        assert_eq!(minimized[0].hypotheses.len(), 1);
        let ranked = rank_candidates(minimized);
        assert_eq!(ranked.len(), 1);
        assert_eq!(ranked[0].candidate.sources[0], "quant-tier4");
    }

    // === §3.4 GF(2) Gröbner theory plugin integration ===

    #[test]
    fn finite_field_plugin_registers_via_builder() {
        let s = Solver::default().with_finite_field(
            adsmt_theory_finite_field::FiniteFieldConfig::default(),
        );
        assert!(
            s.theories
                .theories()
                .iter()
                .any(|t| t.name() == "FiniteField"),
            "FiniteField theory not found in Combination roster",
        );
    }

    #[test]
    fn finite_field_disabled_default_does_not_intervene() {
        // Default config: periodic_interval = 0, try_at_budget_exhaustion = false.
        // The plugin must not change verdicts for instances CDCL
        // already decides.
        let p = Term::var("ff_default_p", Type::bool_());
        let mut s = Solver::default().with_finite_field(
            adsmt_theory_finite_field::FiniteFieldConfig::default(),
        );
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        let r = s.check_sat();
        // CDCL detects the polarity contradiction on its own.
        assert!(matches!(r, SatResult::Unsat { .. }));
    }

    #[test]
    fn finite_field_budget_exhaustion_converts_unknown_to_unsat() {
        // Force CDCL to give up by passing an already-elapsed
        // deadline.  Without `try_at_budget_exhaustion = true`
        // this would surface as Unknown; with it on, the GF(2)
        // Gröbner pass kicks in and certifies UNSAT on
        // `(x) ∧ (¬x)`.
        let p = Term::var("ff_budget_p", Type::bool_());
        let mut s = Solver::default().with_finite_field(
            adsmt_theory_finite_field::FiniteFieldConfig {
                periodic_interval: 0,
                try_at_budget_exhaustion: true,
            },
        );
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());
        let past_deadline = std::time::Instant::now()
            - std::time::Duration::from_millis(1);
        let r = s.check_sat_with_deadline(Some(past_deadline));
        assert!(
            matches!(r, SatResult::Unsat { .. }),
            "expected Unsat via FiniteField fallback, got {r:?}",
        );
    }

    #[test]
    fn finite_field_mut_returns_registered_handle() {
        let mut s = Solver::default().with_finite_field(
            adsmt_theory_finite_field::FiniteFieldConfig {
                periodic_interval: 7,
                try_at_budget_exhaustion: false,
            },
        );
        let ff = s.finite_field_mut().expect("plugin registered");
        assert_eq!(ff.config().periodic_interval, 7);
    }

    #[test]
    fn finite_field_unregistered_returns_none() {
        let mut s = Solver::default();
        assert!(s.finite_field_mut().is_none());
    }

    // §3.5.F regression — guard-evaluation gate semantics.

    #[test]
    fn replay_returns_guards_passed_on_empty_guard_set() {
        let s = Solver::default();
        let trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        let outcome = s.replay_aot_cdcl_trace(&trace, &[]);
        assert_eq!(outcome, ReplayOutcome::GuardsPassed);
    }

    #[test]
    fn replay_returns_guard_miss_on_failed_skeleton_guard() {
        let s = Solver::default();
        let mut trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        // Live skeleton seeded as `SkeletonShape(0)` by the v0
        // dispatcher; a guard pinned to a non-zero hash will
        // miss.
        trace.guards.push(adsmt_jit::JitGuard::SkeletonShape(
            adsmt_jit::SkeletonShape(0xdead_beef),
        ));
        let outcome = s.replay_aot_cdcl_trace(&trace, &[]);
        assert_eq!(outcome, ReplayOutcome::GuardMiss);
    }

    #[test]
    fn replay_returns_guards_passed_when_equiv_class_holds() {
        let s = Solver::default();
        let mut trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        trace.guards.push(adsmt_jit::JitGuard::EquivClass {
            a: "a".to_string(),
            b: "b".to_string(),
        });
        let classes = vec![("a".to_string(), 1), ("b".to_string(), 1)];
        let outcome = s.replay_aot_cdcl_trace(&trace, &classes);
        assert_eq!(outcome, ReplayOutcome::GuardsPassed);
    }
}
