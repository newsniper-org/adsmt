//! Public `Solver` API.

use std::collections::HashMap;

use indexmap::IndexSet;

use adsmt_abduce::abducible::AbducibleSet;
use adsmt_abduce::sld::SldEngine;
use adsmt_abduce::workflow::AbductionState;
use adsmt_abduce::{minimize, rank_candidates, MinimizePolicy};
use adsmt_cert::canonical::Sequent;
use adsmt_cert::witness::TheoryWitness;
use adsmt_cert::{CertBuilder, StepBody, StepId};
use adsmt_core::{Term, TermInner};
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
/// guard-evaluation gate + minimal event-replay scan.
#[derive(Clone, Debug)]
pub enum ReplayOutcome {
    /// At least one of the trace's guards no longer holds
    /// against the current engine state; the caller should
    /// fall through to the regular `check_sat_with_deadline`
    /// path.  v0 uses the agreed "full discard on miss"
    /// semantic from the §3.5 counter-ack §5.4 — partial-replay
    /// fallback is the v1 follow-up that consumes
    /// `CdclTrace::checkpoints`.
    GuardMiss,
    /// Every guard held but the dispatcher chose not to fire
    /// the trace's `events` end-to-end (e.g. the trace carries
    /// no decisive event, or the v0.x dispatcher's
    /// internal-consistency scan deferred to full CDCL).  The
    /// caller falls through to `check_sat_with_deadline` the
    /// same way `GuardMiss` does.
    GuardsPassed,
    /// Every guard held + the v0.x event-replay scan reached
    /// the recorded verdict without re-entering CDCL.  The
    /// `verdict` is the [`SatResult`] the dispatcher
    /// reconstructed from the trace; the caller surfaces it
    /// directly.
    Replayed { verdict: SatResult },
}

// `adsmt_jit` is the §3.2 / §3.5.D companion crate; `Solver::
// replay_aot_cdcl_trace` borrows its `CdclTrace` / `JitGuard` /
// `check_guard` machinery so the replay path and the recorder
// share one vocabulary (per the §3.5 counter-ack §5.5
// vocabulary-reuse).  No `use` needed — the dep entry in
// Cargo.toml brings the crate into scope; call sites name
// the type via `adsmt_jit::...`.

/// Stable `u32` projection of an atom-key string for the v0.x
/// JIT trace recorder.  The `CdclTraceEvent::Propagate /
/// Decide` variants carry `atom: u32` (a `.luart` v0 pool
/// index when the bake side runs); the in-engine recorder
/// doesn't have a Term-DAG pool to consult, so it surfaces a
/// 32-bit DefaultHasher digest of the atom-key string as a
/// stable surrogate.  Collisions are statistically irrelevant
/// at the trace cache sizes the v0.x dispatcher inspects;
/// the §3.5.F / v1 follow-up replaces this with the real pool
/// index once the engine recorder hooks fire inside CDCL.
fn atom_key_hash_u32(atom_key: &str) -> u32 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;
    let mut h = DefaultHasher::new();
    h.write(atom_key.as_bytes());
    h.finish() as u32
}

/// `CdclEventSink` adapter that funnels every engine-side
/// state-transition event into a borrowed
/// [`adsmt_jit::CdclTracer`].  Atom-key strings flow through
/// [`atom_key_hash_u32`] so the recorded
/// [`adsmt_jit::CdclTraceEvent`]'s `atom: u32` shape stays
/// stable across the recorder ⇔ replay-time guard checks.
///
/// The adapter sits in `solver.rs` rather than `adsmt-jit`
/// because the [`crate::cdcl::CdclEventSink`] trait is
/// `adsmt-engine` private — keeping the impl beside the
/// hook avoids exposing the engine-internal sink trait
/// through the JIT crate's public API.
struct CdclTracerSink<'a> {
    tracer: &'a mut adsmt_jit::CdclTracer,
}

impl crate::cdcl::CdclEventSink for CdclTracerSink<'_> {
    fn on_propagate(&mut self, atom_key: &str, polarity: bool, antecedent: i64) {
        self.tracer.record(adsmt_jit::CdclTraceEvent::Propagate {
            atom: atom_key_hash_u32(atom_key),
            polarity,
            antecedent,
        });
    }

    fn on_conflict(&mut self, learnt: &[(String, bool)], lbd: u32) {
        let learnt_event: Vec<(u32, bool)> = learnt
            .iter()
            .map(|(k, p)| (atom_key_hash_u32(k), *p))
            .collect();
        self.tracer.record(adsmt_jit::CdclTraceEvent::Conflict {
            learnt: learnt_event,
            lbd,
        });
    }

    fn on_backjump(&mut self, to_scope: u32) {
        self.tracer
            .record(adsmt_jit::CdclTraceEvent::Backjump { to_scope });
    }

    fn on_decide(&mut self, atom_key: &str, polarity: bool) {
        self.tracer.record(adsmt_jit::CdclTraceEvent::Decide {
            atom: atom_key_hash_u32(atom_key),
            polarity,
        });
    }

    fn on_restart(&mut self) {
        self.tracer.record(adsmt_jit::CdclTraceEvent::Restart);
    }
}

pub struct Solver {
    scopes: Vec<Scope>,
    theories: Combination,
    /// rc.30 (Y4) — selector name → (constructor name, arg index),
    /// cached from every `declare_datatype` so the assert path can
    /// apply the definitional rewrite `sel(C(a₁..aₙ)) → aᵢ` before
    /// solving (a sound, unconditional selector-reduction pass).
    datatype_selectors: std::collections::HashMap<String, (String, usize)>,
    /// rc.30 (Y4) — tester name (`is-C`) → constructor name `C`, for
    /// the definitional tester rewrite `is-C(D(…)) → (C == D)`.
    datatype_testers: std::collections::HashMap<String, String>,
    /// rc.30 (Y4) — every registered constructor name, so the tester
    /// rewrite only fires when the argument is a *known* constructor
    /// application (otherwise the tester stays uninterpreted).
    datatype_ctors: std::collections::HashSet<String>,
    abducibles: AbducibleSet,
    abduction_state: AbductionState,
    cert_builder: CertBuilder,
    proof_mode: ProofMode,
    /// §3.5.B/C — cached CDCL scope-0 snapshot loaded from a
    /// `.luart-cdcl` v1 artefact via [`Self::with_aot_cdcl`].
    /// Consumed by [`Self::replay_aot_cdcl_trace`]'s replay path
    /// + [`Self::restore_cdcl_state_into`] when constructing
    /// the per-query CDCL fresh state.
    aot_cdcl_state: Option<adsmt_aot::CdclSection>,
    /// rc.20 / verus-fork rc.19 retry — pre-flattened CNF
    /// clause set the `restore_cdcl_state_into` pass lifted
    /// from a `.luart-cdcl` v1 artefact's CDCL section.  Every
    /// per-query `check_sat_with_deadline` prepends these
    /// clauses to the freshly-flattened per-query CNF so the
    /// prelude's clause set does not need to be re-derived from
    /// the (Term, Lit) ground formulas on every `(check-sat)`.
    /// Empty (and therefore zero-cost) unless
    /// `restore_cdcl_state_into` ran.
    aot_prelude_clauses: Vec<crate::cnf::Clause>,
    /// rc.28 (S.1-AOT) / verus-fork rc.27 retry — set when the
    /// baked prelude contained at least one opaque assertion that
    /// `flatten_to_clauses` could not encode (an OR-of-AND or
    /// similar).  Mirrors `check_ground`'s baseline `had_opaque`
    /// bookkeeping onto the `--aot-load` path: a later theory
    /// `Sat` must downgrade to `Unknown` because the dropped
    /// opaque structure might have constrained the model.  An
    /// `Unsat` (empty clause survived into the baked subset) stays
    /// `Unsat` — soundness asymmetry.  Loaded from
    /// `CdclSection::had_opaque` by `restore_cdcl_state_into`.
    aot_prelude_had_opaque: bool,
    /// rc.20 / verus-fork rc.19 retry — set of prelude
    /// assertion `Term`s.  `Term`'s `Hash` / `Eq` impls are
    /// `Arc::ptr_eq`-based (post-rc.10 hash-cons), so a
    /// `HashSet<Term>` lookup is O(1) without the
    /// `to_string()` cost the v0.x prototype paid.
    /// Populated by `with_aot_prelude` so the per-query
    /// `check_sat_with_deadline` can skip re-flattening any
    /// literal whose Term already lives in the cached
    /// `aot_prelude_clauses` payload.
    aot_prelude_term_set: std::collections::HashSet<Term>,
    /// rc.21 / verus-fork rc.20 retry — pool-index → Term
    /// table the `restore_cdcl_state_into` pass kept around
    /// so the `_with_seed` variant's seed-builder can resolve
    /// the CDCL section's trail / VSIDS / saved-phase fields'
    /// `atom_pool_idx: u32` references into engine-side
    /// `atom_key: String` shapes.  Empty unless
    /// `with_aot_cdcl` consumed a `.luart-cdcl` v1 prelude.
    aot_pool_terms: Vec<Term>,
    /// §3.5.D — append-only JIT-trace recorder.  When `Some`,
    /// every CDCL state transition the per-query solve walks
    /// through is appended.  Activated via
    /// [`Self::start_jit_recording`]; drained via
    /// [`Self::take_jit_recording`].
    jit_tracer: Option<adsmt_jit::CdclTracer>,
    /// §3.2 — joint `(JitCache, KernelStore)` registry.  When
    /// `Some`, [`Self::replay_aot_cdcl_trace`]'s `GuardsPassed`
    /// / `Replayed` arms can invoke a registered compiled
    /// kernel after the guard gate; `None` keeps the v0.x
    /// pure-interpreter behaviour.  Activated via
    /// [`Self::start_jit_caching`].
    jit_registry: Option<adsmt_jit::JitRegistry>,
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
            datatype_selectors: std::collections::HashMap::new(),
            datatype_testers: std::collections::HashMap::new(),
            datatype_ctors: std::collections::HashSet::new(),
            abducibles: AbducibleSet::new(),
            abduction_state: AbductionState::new(),
            cert_builder: CertBuilder::new(),
            // v0.15: default to recording certificates. Callers
            // that don't need them can opt out with
            // `.with_proof_mode(ProofMode::None)` to skip the
            // bookkeeping cost.
            proof_mode: ProofMode::Always,
            aot_cdcl_state: None,
            aot_prelude_clauses: Vec::new(),
            aot_prelude_had_opaque: false,
            aot_prelude_term_set: std::collections::HashSet::new(),
            aot_pool_terms: Vec::new(),
            jit_tracer: None,
            jit_registry: None,
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
            // §3.1.D / verus-fork rc.18 retry (c') — drop
            // the per-term `intern_external` call.  Pre-
            // rc.19 every prelude assertion ran through a
            // redundant post-order walk on top of what
            // `adsmt_aot::reconstruct` had already done at
            // file-decode time, paying a recursive cache-
            // hit loop with no observable effect (the
            // reader's `Term::var / Term::const_ / Term::
            // app / Term::lam` chain installs canonical
            // hash-cons entries before this point).  The
            // term enters the cert ledger directly; the
            // hash-cons cache continues to do its job
            // anywhere structurally-equal atoms surface
            // from the per-query input later.
            //
            // rc.20 — stash the prelude term on
            // `Self::aot_prelude_term_set` (Arc::ptr_eq-keyed
            // `HashSet<Term>`) so the per-query
            // `check_sat_with_deadline` can skip re-flattening
            // any assertion already cached in
            // `aot_prelude_clauses`.  No `to_string()` cost —
            // the hash-cons cache makes Term lookup O(1).
            self.aot_prelude_term_set.insert(term.clone());
            let loc = adsmt_cert::SourceLoc::new(0, idx as u32);
            self.assert_at(term, loc);
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
        mut self,
        prelude: adsmt_aot::ReconstructedCdclPrelude,
    ) -> Self {
        // §3.5.C — stash the CDCL scope-0 snapshot on the
        // solver.  At rc.20 the stash flows directly into
        // `restore_cdcl_state_into` so the per-query
        // `check_sat_with_deadline` skips re-flattening the
        // prelude on every `(check-sat)`.  The prelude
        // assertions still thread through `with_aot_prelude`
        // for the cert ledger / `(get-unsat-core)` / audit
        // surface, so callers that ignore the CDCL snapshot
        // (e.g. legacy v0 readers) keep seeing the prelude
        // axioms as if `with_aot_prelude` had been called
        // directly.
        if let Some(section) = prelude.cdcl_section.as_ref() {
            self.restore_cdcl_state_into(section, &prelude.prelude.pool_terms);
        }
        // rc.21 — stash the pool terms so the
        // `cdcl_solve_with_model_deadline_with_seed` builder
        // can resolve the v1 section's `atom_pool_idx: u32`
        // references when assembling the BCP-fixpoint seed.
        self.aot_pool_terms = prelude.prelude.pool_terms.clone();
        self.aot_cdcl_state = prelude.cdcl_section;
        self.with_aot_prelude(prelude.prelude)
    }

    /// rc.20 / verus-fork rc.19 retry §3.5.J gate — consume a
    /// `.luart-cdcl` v1 [`adsmt_aot::CdclSection`] and rebuild
    /// the engine-side CNF clause set the bake side captured.
    ///
    /// v0.x scope (this rev): the section's `clauses` field is
    /// projected back into `Vec<crate::cnf::Clause>` and stashed
    /// on `Self::aot_prelude_clauses`.  Every per-query
    /// `check_sat_with_deadline` prepends the stash to the
    /// freshly-flattened CNF before running CDCL, so the
    /// prelude's clause set does not need to be re-derived from
    /// the assertion DAG on every `(check-sat)`.  This is the
    /// single largest payoff the §3.5.J smoke matrix expected
    /// from `restore_cdcl_state_into`'s landing — the §1.1 bake
    /// captures clauses + trail + watches + VSIDS + saved-phase
    /// in the artefact, the load side picks up the clause vec
    /// here.
    ///
    /// Trail / watches / VSIDS / saved-phase are *not* restored
    /// at this rev — the engine's CDCL inner loop allocates its
    /// own `CdclState::new()` per call.  Promoting the
    /// remaining four CDCL state fields needs a CDCL-loop
    /// signature change (a `_with_seed` variant of
    /// `cdcl_solve_with_model_deadline`) and lands in the
    /// follow-up.  The clause-set cache lifted by the v0.x
    /// scope here already shortcuts the bulk of the work the
    /// verus_smoke prelude pays per-`(check-sat)`.
    ///
    /// `pool_terms` is the index → `Term` map
    /// `adsmt_aot::reader::reconstruct` produced; we use it to
    /// translate the section's `atom_pool_idx: u32` references
    /// back into engine-side `Lit::atom: Term` shapes.
    pub fn restore_cdcl_state_into(
        &mut self,
        section: &adsmt_aot::CdclSection,
        pool_terms: &[adsmt_core::Term],
    ) {
        let mut clauses: Vec<crate::cnf::Clause> = Vec::with_capacity(section.clauses.len());
        for c in &section.clauses {
            let mut lits: Vec<crate::cnf::Lit> = Vec::with_capacity(c.lits.len());
            // rc.28 (S.1-AOT): an empty `c.lits` is a *genuine*
            // empty clause — the flattened `(assert false)` /
            // `(assert (not true))` contradiction baked into the
            // prelude — and MUST be kept so the seeded CDCL solve
            // sees the conflict and returns `unsat`.  Only the
            // defensive out-of-range case below drops the clause,
            // tracked by `ok` so we never confuse "decode failure,
            // drop" with "genuinely empty, keep".  Before rc.28 the
            // blanket `if !lits.is_empty()` silently swallowed the
            // empty clause, which is exactly the AOT-load
            // `sat`-for-unsat soundness gap verus-fork reported.
            let mut ok = true;
            for (atom_idx, polarity) in &c.lits {
                let Some(atom) = pool_terms.get(*atom_idx as usize).cloned() else {
                    // Defence-in-depth: out-of-range atom
                    // index in the v1 section.  Drop the
                    // entire clause rather than emit a bogus
                    // Lit; v1 readers already reject this
                    // shape on decode but the cross-check is
                    // cheap.
                    ok = false;
                    break;
                };
                lits.push(crate::cnf::Lit {
                    atom,
                    polarity: *polarity,
                });
            }
            if ok {
                clauses.push(lits);
            }
        }
        self.aot_prelude_clauses = clauses;
        self.aot_prelude_had_opaque = section.had_opaque;
    }

    /// rc.20 read-only borrow of the prelude clause-set cache
    /// — used by `check_sat_with_deadline` to prepend the
    /// cached clauses to the freshly-flattened per-query CNF
    /// before running CDCL.  Empty until
    /// [`Self::restore_cdcl_state_into`] runs.
    pub fn aot_prelude_clauses(&self) -> &[crate::cnf::Clause] {
        &self.aot_prelude_clauses
    }

    /// rc.21 / verus-fork rc.20 retry §3.5.J gate — build the
    /// `CdclState` seed
    /// [`crate::cdcl::cdcl_solve_with_model_deadline_with_seed`]
    /// consumes.  Translates the stashed `.luart-cdcl` v1 CDCL
    /// section's `trail` / `activity` / `saved_phase` records
    /// (which carry `atom_pool_idx: u32` references) into the
    /// engine-side `atom_key: String` shapes the CDCL inner
    /// loop expects.
    ///
    /// Returns `None` when no v1 artefact has been loaded —
    /// the seed-aware CDCL entry point falls through to the
    /// fresh-state path in that case.
    ///
    /// The `watches` / `clause_watches` fields are *not*
    /// populated here — the v1 section's watch-graph indices
    /// are stale against the per-query clause vector, so the
    /// CDCL inner loop rebuilds them via `build_watches`
    /// after consuming the seed.
    fn prepare_cdcl_seed(&self) -> Option<crate::cdcl::CdclState> {
        let section = self.aot_cdcl_state.as_ref()?;
        if self.aot_pool_terms.is_empty() {
            return None;
        }
        let mut state = crate::cdcl::CdclState::default();
        let pool = &self.aot_pool_terms;
        // Trail — every entry the v1 section captured is at
        // decision level 0 (BCP fixpoint, no decisions yet),
        // so we tag each with `decision_level = 0` regardless
        // of what the on-disk `reason_clause_idx` field
        // implied.  The `Reason::Decision` synthetic shape is
        // safe at root level — conflict analysis short-circuits
        // before walking past it.
        for entry in &section.trail {
            let term = pool.get(entry.atom_pool_idx as usize)?.clone();
            state.assign.insert(term.clone(), entry.polarity);
            state.trail.push(crate::cdcl::TrailEntry {
                atom: term,
                polarity: entry.polarity,
                decision_level: 0,
                reason: crate::cdcl::Reason::Decision,
            });
        }
        for entry in &section.vsids {
            let term = pool.get(entry.atom_pool_idx as usize)?.clone();
            state.activity.insert(term, entry.activity);
        }
        for entry in &section.saved_phase {
            let term = pool.get(entry.atom_pool_idx as usize)?.clone();
            state.saved_phase.insert(term, entry.polarity);
        }
        Some(state)
    }

    /// §3.5.B real-bake helper — flatten every assertion the
    /// solver currently holds into CNF, then run initial BCP to
    /// fixpoint without making any decisions.  Returns the
    /// resulting `(clauses, state)` pair so callers (e.g.
    /// `lu-smt --aot-bake --aot-include-cdcl`) can serialise it
    /// into a `.luart-cdcl` v1 [`adsmt_aot::CdclSection`].
    ///
    /// Stays Term-DAG-agnostic — the `state.trail[*].atom_key`
    /// `String` rendering of `Lit::atom: Term` is what callers
    /// map to the `.luart` v0 pool index they own; the engine
    /// does not know about the pool layout.
    pub fn dump_cdcl_state(
        &self,
    ) -> (Vec<crate::cnf::Clause>, crate::cdcl::CdclState, bool) {
        let mut all_clauses: Vec<crate::cnf::Clause> = Vec::new();
        // rc.28 (S.1-AOT) — track whether any assertion is
        // un-encodable, so the baked section can carry the
        // `had_opaque` flag the load-side `check_ground` needs to
        // downgrade a `Sat` to `Unknown` (mirroring the baseline
        // soundness fix).  An opaque assertion's clauses are
        // dropped here (the `Some` arm only appends what flattens),
        // exactly as the baseline drops them — but the flag
        // records the drop so the verdict stays honest at load.
        let mut had_opaque = false;
        for term in self.all_assertions() {
            match crate::cnf::flatten_to_clauses(&term) {
                Some(mut cs) => all_clauses.append(&mut cs),
                None => had_opaque = true,
            }
        }
        let state = crate::cdcl::initial_bcp(&all_clauses);
        (all_clauses, state, had_opaque)
    }

    /// §3.5.B / `--aot-include-cdcl` consumer — read-only
    /// borrow of the cached CDCL snapshot (if any) that was
    /// installed via [`Self::with_aot_cdcl`].  Returns `None`
    /// for solvers loaded from a v0 `.luart` artefact (or
    /// constructed without ever loading one).
    pub fn aot_cdcl_state(&self) -> Option<&adsmt_aot::CdclSection> {
        self.aot_cdcl_state.as_ref()
    }

    /// §3.5.D recorder activation — install an empty
    /// [`adsmt_jit::CdclTracer`] so subsequent
    /// `(check-sat)` calls append CDCL state transitions to
    /// it.  Idempotent: calling twice resets the recorder.
    pub fn start_jit_recording(&mut self) {
        self.jit_tracer = Some(adsmt_jit::CdclTracer::new());
    }

    /// §3.5.D recorder drain — pull the active tracer (if any)
    /// out of the solver.  Returns `None` if no recording was
    /// started via [`Self::start_jit_recording`].
    pub fn take_jit_recording(&mut self) -> Option<adsmt_jit::CdclTracer> {
        self.jit_tracer.take()
    }

    /// §3.2 registry activation — install an empty
    /// [`adsmt_jit::JitRegistry`] so subsequent
    /// `Self::register_jit_trace` calls emit + cache
    /// compiled kernels.  Idempotent: calling twice resets
    /// the registry.
    pub fn start_jit_caching(&mut self) {
        self.jit_registry = Some(adsmt_jit::JitRegistry::new());
    }

    /// §3.2 — register a recorded trace with the JIT
    /// registry.  No-op + `Ok(None)` when the registry is
    /// not active; otherwise emits a kernel + caches the
    /// trace + returns the assigned kernel id.
    pub fn register_jit_trace(
        &mut self,
        trace: adsmt_jit::Trace,
    ) -> Result<Option<u32>, adsmt_jit::KernelError> {
        match self.jit_registry.as_mut() {
            Some(registry) => Ok(Some(registry.register_trace(trace)?)),
            None => Ok(None),
        }
    }

    /// §3.2 — read-only borrow of the JIT registry (if any).
    /// Used by `replay_aot_cdcl_trace`'s post-guard hook +
    /// integration tests.
    pub fn jit_registry(&self) -> Option<&adsmt_jit::JitRegistry> {
        self.jit_registry.as_ref()
    }

    /// §3.5.F replay dispatcher (v0 skeleton).  Evaluates every
    /// guard in `trace.guards` + the end-of-trace
    /// `GF2Snapshot`-derived basis against the current
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
        // §3.5.F live-skeleton computation — depth-3
        // SkeletonShape hash of the per-query top-level
        // formula.  The v0 dispatcher hard-coded
        // `SkeletonShape(0)`; promoting the computation here
        // makes `JitGuard::SkeletonShape` checks consult the
        // actual query rather than the constant.
        let live_skeleton = self.compute_live_skeleton();
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
        // §3.5.F v0.x event-replay scan.  Rather than
        // re-firing each recorded event through the live CDCL
        // state machine (the full restoration path that v1
        // unlocks via `restore_cdcl_state_into`), the v0.x
        // dispatcher walks the trace's `events` and reaches a
        // verdict iff the event sequence is *internally
        // consistent and decisive*:
        //   - `events.is_empty()`            → Sat (vacuous)
        //   - any `Conflict { … }` at the     → Unsat
        //     top of the sequence
        //   - otherwise                       → fall through
        //                                       (GuardsPassed)
        // The conservative arm preserves the v0 fall-through
        // semantics — a guard-pass with no decisive event
        // makes the caller run regular `check_sat_with_deadline`
        // exactly as before.
        // §3.2 compiled-kernel invocation (v0.x post-guard
        // hook).  When the JIT registry is active + the
        // trace was previously registered via
        // `register_jit_trace`, lookup the compiled kernel
        // and invoke it before the event-replay scan.  v0.x
        // kernels are `emit_noop_kernel`-produced (zero
        // payload — a single `xor rax, rax; ret`), so the
        // invocation is observable only as a function-call
        // overhead.  Specialised kernels lifted from
        // `trace.events` land alongside the v1 follow-up.
        if let Some(registry) = self.jit_registry.as_ref()
            && let Some(kernel) = registry.lookup_kernel(
                live_skeleton,
                &trace.signature.basis,
                classes,
            )
        {
            // SAFETY: the noop kernel emitted by
            // `emit_noop_kernel` matches the `unsafe extern
            // "C" fn() -> i64` shape; v0.x guarantees no
            // other emitter is in flight.
            let _ = unsafe { kernel.invoke() };
        }

        if trace.events.is_empty() {
            return ReplayOutcome::Replayed {
                verdict: SatResult::Sat { model: crate::result::Model::new() },
            };
        }
        let has_conflict = trace.events.iter().any(|e| {
            matches!(e, adsmt_jit::CdclTraceEvent::Conflict { .. })
        });
        let has_restart = trace.events.iter().any(|e| {
            matches!(e, adsmt_jit::CdclTraceEvent::Restart)
        });
        if has_conflict && !has_restart {
            return ReplayOutcome::Replayed {
                verdict: SatResult::Unsat {
                    certificate: None,
                    core: crate::result::UnsatCore::new(),
                },
            };
        }
        ReplayOutcome::GuardsPassed
    }

    /// Internal helper — depth-3 skeleton hash of the
    /// per-query top-level formula.  v0.x reads the first
    /// asserted term (the most-recently-pushed top-level fact
    /// the engine has not yet popped) as the representative;
    /// an empty assertion ledger surfaces `SkeletonShape(0)`.
    fn compute_live_skeleton(&self) -> adsmt_jit::SkeletonShape {
        if let Some(first) = self.all_assertions().first() {
            adsmt_jit::SkeletonShape::of(first)
        } else {
            adsmt_jit::SkeletonShape(0)
        }
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
        // rc.30 — cache selectors / testers / constructor names for
        // the engine-side normalization pass (assert_with_polarity_at).
        for (ci, ctor) in decl.constructors.iter().enumerate() {
            self.datatype_ctors.insert(ctor.clone());
            self.datatype_testers
                .insert(format!("is-{ctor}"), ctor.clone());
            if let Some(sels) = decl.selectors.get(ci) {
                for (si, sel) in sels.iter().enumerate() {
                    self.datatype_selectors
                        .insert(sel.clone(), (ctor.clone(), si));
                }
            }
        }
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
    /// rc.30 (Y4) — definitional selector reduction:
    /// rewrite every `sel(C(a₁..aₙ))` sub-term to `aᵢ` (where `sel`
    /// is the `i`-th selector of constructor `C`).  This is the
    /// selector axiom applied as an unconditional rewrite — sound
    /// (the field value equals the selector applied to the
    /// constructor) and it makes selector reasoning complete without
    /// depending on which sort the enclosing literal routes to.
    fn normalize_selectors(&self, t: &Term) -> Term {
        if self.datatype_selectors.is_empty() && self.datatype_testers.is_empty() {
            return t.clone();
        }
        match t.kind() {
            TermInner::App(f, x) => {
                let nf = self.normalize_selectors(f);
                let nx = self.normalize_selectors(x);
                let head_name = match nf.kind() {
                    TermInner::Const(c) => Some(c.name.clone()),
                    TermInner::Var(v) => Some(v.name.clone()),
                    _ => None,
                };
                if let Some(name) = head_name {
                    // `sel(C(args))` → `args[idx]`.
                    if let Some((ctor, idx)) = self.datatype_selectors.get(&name)
                        && let Some((cname, args)) = decompose_app(&nx)
                        && &cname == ctor
                        && *idx < args.len()
                    {
                        return args[*idx].clone();
                    }
                    // `is-C(D(args))` → `true`/`false` when `D` is a
                    // known constructor (otherwise stays uninterpreted).
                    if let Some(ctor) = self.datatype_testers.get(&name)
                        && let Some((cname, _)) = decompose_app(&nx)
                        && self.datatype_ctors.contains(&cname)
                    {
                        return if &cname == ctor {
                            Term::true_const()
                        } else {
                            Term::false_const()
                        };
                    }
                }
                Term::app(nf, nx).unwrap_or_else(|_| t.clone())
            }
            // Ground assertions are quantifier-free post-skolemization;
            // datatype apps under a binder are left to the (routed)
            // theory-level reduction.
            _ => t.clone(),
        }
    }

    pub fn assert_with_polarity_at(
        &mut self,
        t: Term,
        polarity: bool,
        loc: Option<adsmt_cert::SourceLoc>,
    ) {
        let t = self.normalize_selectors(&t);
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

        // §1.3 / §3.5.D engine recorder hook (rc.17+).  The
        // tracer is now wired through `cdcl::*_recording`'s
        // inner-loop sink (see `check_sat_inner`'s
        // model-carrying CDCL path), so every state
        // transition the engine walks through is captured
        // per-Propagate / per-Conflict / per-Backjump /
        // per-Decide / per-Restart.
        //
        // rc.21 / verus-fork rc.20 retry (b''') — session
        // boundary fallback.  Some exit paths surface
        // SatResult::Unknown without the inner-loop sink ever
        // firing (deadline-cancel inside `flatten_to_clauses`,
        // theory check on a quantifier-heavy prelude that
        // never reaches CDCL, etc.).  The verus-fork retry
        // measured this on the verus_smoke prelude — Unknown
        // verdicts dropped a 56-byte header-only `.lutrace`.
        // The fallback below records a single Restart event
        // (and on the verdict side, a Conflict or Decide
        // shape) when the tracer is active and otherwise
        // empty, so the load-back path's session-shape
        // diagnostics always have *something* to inspect.
        if let Some(tracer) = self.jit_tracer.as_mut()
            && tracer.is_empty()
        {
            tracer.record(adsmt_jit::CdclTraceEvent::Restart);
            match &original_result {
                SatResult::Unsat { .. } => {
                    tracer.record(adsmt_jit::CdclTraceEvent::Conflict {
                        learnt: Vec::new(),
                        lbd: 0,
                    });
                }
                SatResult::Sat { model } => {
                    for (atom, polarity) in &model.bool_assignments {
                        let atom_u32 = atom_key_hash_u32(atom);
                        tracer.record(adsmt_jit::CdclTraceEvent::Decide {
                            atom: atom_u32,
                            polarity: *polarity,
                        });
                    }
                }
                _ => {}
            }
        }

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
        // rc.24 (e'''.2) — `instantiations` is an
        // `IndexSet<Term>`, not a `Vec<Term>`.  The three
        // dedup sites below were each
        // `if !instantiations.iter().any(|t| t.alpha_eq(&inst))`
        // — an O(N) scan per candidate instantiation, quadratic
        // across the quantifier loop on a verus_smoke-sized
        // prelude.  `IndexSet::insert` dedups in O(1) on the
        // rc.10 hash-cons handles while preserving insertion
        // order (the `for inst in &instantiations` rebuild of
        // `combined` + the `instantiations.len()` fixpoint check
        // both stay deterministic).
        let mut instantiations: IndexSet<Term> = IndexSet::new();
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
                            instantiations.insert(inst);
                        }
                        // Tier 2: conflict-based — pick instantiations
                        // that directly contradict an existing negative
                        // ground assertion.
                        for inst in crate::quant_conflict::conflict_instantiate(var, body, &rest) {
                            instantiations.insert(inst);
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
                                instantiations.insert(inst);
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
        // rc.20 / verus-fork rc.19 retry §3.5.J gate — skip
        // any prelude assertion the `restore_cdcl_state_into`
        // pass already lifted into `aot_prelude_clauses`.  The
        // per-query CNF flatten step below then runs over the
        // delta only.
        let lits: Vec<_> = if !self.aot_prelude_clauses.is_empty() {
            lits.into_iter()
                .filter(|(t, _)| !self.aot_prelude_term_set.contains(t))
                .collect()
        } else {
            lits
        };
        // (1) Decompose every asserted (term, polarity) into CNF clauses.
        let mut clauses: Vec<Clause> = Vec::new();
        // rc.27 (S.1) — set when *some* assertion's boolean
        // structure is not CNF-encodable by the v0.3 flattener
        // (e.g. a nested OR-of-AND, or a term exceeding
        // `MAX_FLATTEN_NODES`).  Such an assertion is *skipped*
        // from the clause set rather than routed to a theory-only
        // path that drops the whole accumulator — see the `None`
        // arm below.  The flag downgrades a final `Sat` verdict to
        // `Unknown` (we cannot claim satisfiability while ignoring
        // an assertion we could not encode), while leaving `Unsat`
        // sound (the flattenable subset being unsat ⟹ the full,
        // larger constraint set is unsat).
        // rc.28 (S.1-AOT): seed from the baked-prelude flag so an
        // opaque assertion that was dropped at *bake* time still
        // forces the `Sat`→`Unknown` downgrade on the `--aot-load`
        // path, exactly as a per-query opaque assert does on the
        // baseline path.  `false` for any non-AOT solve.
        let mut had_opaque = self.aot_prelude_had_opaque;
        // rc.20 — prepend the prelude clause-set cache when
        // `restore_cdcl_state_into` has populated it.  v0.x
        // scope ships the clause vec only; trail / watches /
        // VSIDS / saved-phase restoration sits behind the
        // CDCL-loop signature change queued for the follow-up.
        clauses.extend(self.aot_prelude_clauses.iter().cloned());
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
                    // rc.27 (S.1) — soundness fix.  Pre-rc.27 this
                    // did `return self.check_via_theories(&lits)`,
                    // which **abandoned the entire `clauses`
                    // accumulator** (including the empty clause an
                    // `(assert false)` contributes) and re-routed
                    // through the theory path — and that path skips
                    // every compound `and`/`or`/`=>` term and never
                    // evaluates a bare propositional `false`, so it
                    // returned an unsound `sat` whenever an
                    // un-flattenable assertion co-occurred with a
                    // contradiction (verus-fork rc.26 retry P0:
                    // `(=> P (and Q R))` + `(assert false)` → `sat`).
                    //
                    // The sound behaviour: keep the flattenable
                    // clauses (skip *only* this un-encodable
                    // assertion) and mark `had_opaque`.  The SAT
                    // solve below then runs on the flattenable
                    // subset; if that is unsat the whole set is
                    // unsat (sound), and if it is sat the verdict
                    // downgrades to `Unknown` rather than claiming a
                    // satisfiability we cannot justify.
                    had_opaque = true;
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
        // rc.21 / verus-fork rc.20 retry §3.5.J gate — when
        // the v1.1 artefact's CDCL section sits stashed on
        // `self.aot_cdcl_state`, build a seed from it so the
        // first Luby epoch's `cdcl_solve_with_model_deadline`
        // call reuses the BCP-fixpoint trail / VSIDS / saved-
        // phase the bake side captured.  This is the piece
        // that finally drops the §3.5.J wall below the
        // ~5.3 s prelude-BCP floor the v0.x clause-cache
        // shortcut left in place.
        //
        // §1.3 v1 / verus-fork rc.19 retry (b'') — when the
        // JIT tracer is active, route the satisfiability-only
        // first stage through the recording variant so the
        // recorder captures events on Unsat / Unknown verdicts
        // (pre-rc.20 only the model-carrying second-stage call
        // ran through the recording variant, so Sat traces
        // populated but Unsat / deadline-cancelled
        // `(check-sat)`s emitted vacuous artefacts).
        //
        // Note: the seed-aware `_recording` variant doesn't
        // exist yet; tracer-active + seed-active is rare in
        // practice (tracer for warm-up runs, seed for
        // per-query runs), so the v0.x scope picks
        // whichever takes priority on the live path —
        // recording wins when both are set, because losing a
        // ~5.3 s shortcut to log per-event Propagate stream
        // is acceptable for a one-shot diagnostic run, while
        // losing the per-query shortcut is a recurring cost.
        #[cfg(not(any(feature = "oxiz", feature = "cadical")))]
        let sat_result = if self.jit_tracer.is_some() {
            let mut sink = CdclTracerSink {
                tracer: self
                    .jit_tracer
                    .as_mut()
                    .expect("is_some checked above"),
            };
            crate::cdcl::cdcl_with_restarts_deadline_recording(
                &clauses, 64, 12, deadline, &mut sink,
            )
        } else {
            let seed = self.prepare_cdcl_seed();
            crate::cdcl::cdcl_with_restarts_deadline_with_seed(
                &clauses, 64, 12, deadline, seed,
            )
        };
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
                // §1.3 / §3.5.D — when the JIT tracer is
                // active, route the model-carrying CDCL run
                // through the recording variant so every
                // `Propagate` / `Conflict` / `Backjump` /
                // `Decide` / `Restart` transition is
                // captured for the §3.5.G `.lutrace`
                // artefact (the verus-fork rc.17 retry
                // pointed at this hook as the gating piece
                // for a non-vacuous trace on the
                // verus_smoke prelude).
                let model = if self.jit_tracer.is_some() {
                    let mut sink = CdclTracerSink {
                        tracer: self.jit_tracer.as_mut().expect(
                            "is_some checked above",
                        ),
                    };
                    match crate::cdcl::cdcl_with_restarts_with_model_deadline_recording(
                        &clauses,
                        64,
                        12,
                        deadline,
                        &mut sink,
                    ) {
                        crate::cdcl::CdclOutcome::Sat { model } => model,
                        _ => HashMap::new(),
                    }
                } else {
                    let seed = self.prepare_cdcl_seed();
                    match crate::cdcl::cdcl_with_restarts_with_model_deadline_with_seed(
                        &clauses,
                        64,
                        12,
                        deadline,
                        seed,
                    ) {
                        crate::cdcl::CdclOutcome::Sat { model } => model,
                        _ => HashMap::new(),
                    }
                };
                if expired(deadline) {
                    return SatResult::Unknown {
                        reason: "rlimit exceeded".to_string(),
                    };
                }
                let theory_result =
                    self.check_via_theories_with_model(&lits, &clauses, model, deadline);
                // rc.27 (S.1) — never report `sat` when some
                // assertion was un-encodable: the flattenable
                // subset is satisfiable but the opaque remainder
                // is unresolved, so the honest verdict is
                // `Unknown`.  (`Unsat` / `Unknown` from the theory
                // layer pass through unchanged — both are sound
                // even with an ignored constraint.)
                if had_opaque
                    && matches!(theory_result, SatResult::Sat { .. })
                {
                    return SatResult::Unknown {
                        reason: "assertion set contains a boolean structure \
                                 the CNF flattener cannot encode (e.g. nested \
                                 OR-of-AND); the flattenable subset is \
                                 satisfiable but the un-encoded assertions are \
                                 unresolved"
                            .to_string(),
                    };
                }
                theory_result
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
    /// [`check_via_theories_with_model`]) feed positions through
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

    /// rc.33 (verus-fork "Gap A") — build a certificate for an `unsat`
    /// reached by **delegation**: the native engine returned `Unknown`
    /// (or the session was `degraded`) and an external solver — OxiZ —
    /// decided the buffered SMT-LIB `unsat`. Without this the delegated
    /// verdict carried no cert, so `--emit-cert*` was a no-op on every
    /// real (Poly/fuel-prelude) obligation Verus verifies.
    ///
    /// The cert records each asserted formula as an `Assume` and a
    /// final `⊢ false` justified by an opaque `oxiz-delegation`
    /// witness; an ITP emitter renders that final step as an axiom —
    /// adsmt produced no kernel proof here, it trusted the delegate,
    /// the same trust status the SAT/DRAT step already has. Built on a
    /// **fresh** [`CertBuilder`] so it is independent of any partial
    /// state the inconclusive native check left in `self.cert_builder`.
    /// `None` under [`ProofMode::None`].
    pub fn build_delegated_unsat_cert(
        &self,
        delegate: &str,
    ) -> Option<adsmt_cert::Certificate> {
        if matches!(self.proof_mode, ProofMode::None) {
            return None;
        }
        let mut builder = CertBuilder::new();
        let mut assume_ids: Vec<StepId> = Vec::new();
        let mut hyps: Vec<Term> = Vec::new();
        for phi in self.all_assertions() {
            let id = builder.add(
                StepBody::Assume(phi.clone()),
                Sequent { hyps: vec![phi.clone()], concl: phi.clone() },
            );
            assume_ids.push(id);
            hyps.push(phi);
        }
        let witness = TheoryWitness::Opaque {
            kind: "oxiz-delegation".into(),
            notes: format!("unsat decided by the delegated solver ({delegate})"),
        };
        let conclusion = builder.add(
            StepBody::Theory {
                name: "delegation".into(),
                witness,
                parents: assume_ids,
            },
            Sequent { hyps, concl: Term::false_const() },
        );
        Some(builder.snapshot(conclusion))
    }

    /// Route raw literals through the theory layer, threading the
    /// boolean assignment from the SAT layer through to the
    /// verdict's `SatResult::Sat::model`.
    ///
    /// rc.27 (S.1) — the no-model `check_via_theories` wrapper was
    /// removed when the opaque-flatten fallback that called it
    /// (`return self.check_via_theories(&lits)`) was replaced by
    /// the sound `had_opaque` path; this is the only theory-route
    /// entry point now, always reached *after* the SAT solve on
    /// the flattenable clause subset.
    fn check_via_theories_with_model(
        &mut self,
        lits: &[(Term, bool)],
        clauses: &[Clause],
        bool_assignment: HashMap<String, bool>,
        deadline: Option<std::time::Instant>,
    ) -> SatResult {
        self.theories.reset();
        // rc.27 (S.3) — defence-in-depth: the theory layer only
        // reasons about equalities and never evaluates a bare
        // propositional constant, so an asserted `false` (or
        // `(not true)`) that reaches this path must short-circuit
        // to `Unsat` *before* `dpllt::run_once` — otherwise the
        // theory loop would return `Sat` for an obviously
        // contradictory set.  With the (S.1) fix above this path
        // no longer receives the empty-clause-bearing accumulator,
        // but the guard is cheap and closes the hole independently.
        for (t, p) in lits {
            let asserts_false = (*p && t.is_false_const())
                || (!*p && t.is_true_const());
            if asserts_false {
                let witness = TheoryWitness::Opaque {
                    kind: "propositional".into(),
                    notes: "asserted constant false".into(),
                };
                let lits_with_locs = self.attach_locs(lits);
                let cert = self.build_unsat_cert_opt_with_locs(
                    &lits_with_locs,
                    "propositional",
                    witness,
                );
                let core =
                    crate::result::UnsatCore::from_assertions(&self.all_assertions());
                return SatResult::Unsat { certificate: cert, core };
            }
        }
        // ── Stage 1: forced literals ── can soundly conclude `Unsat`.
        //
        // rc.32.x: the prior code routed only top-level *atomic* literals
        // and skipped every `and`/`or`/`=>` wholesale — so the conjuncts
        // of `(assert (and (> x 0) (< x 0)))` never reached LinArith and
        // the formula was an unsound `sat`. A conjunct of an asserted
        // conjunction MUST hold in every model, so `collect_forced_literals`
        // descends through asserted-true `and` (and the De Morgan duals
        // `¬(A∨B)`, `¬(A⇒B)`) to surface the *entailed* literals, leaving
        // genuine disjunctions opaque. Routing only forced literals keeps
        // `Unsat` sound: every routed literal is entailed, so theory-
        // infeasibility of the routed set ⟹ the whole set is unsat.
        let mut forced: Vec<(Term, bool)> = Vec::new();
        for (t, p) in lits {
            collect_forced_literals(t, *p, &mut forced);
        }
        let forced_uninterpreted = match dpllt::run_once_with_deadline(
            &mut self.theories,
            &forced,
            deadline,
        ) {
            LoopOutcome::Unsat { theory, witness } => {
                // Theory unsat threads `:loc` through the cert exactly
                // like the SAT-level unsat path.
                let lits_with_locs = self.attach_locs(lits);
                let cert = self.build_unsat_cert_opt_with_locs(
                    &lits_with_locs,
                    &theory,
                    witness,
                );
                let core = crate::result::UnsatCore::from_assertions(&self.all_assertions());
                return SatResult::Unsat { certificate: cert, core };
            }
            LoopOutcome::Unknown { theory, reason } => {
                return SatResult::Unknown { reason: format!("{theory}: {reason}") };
            }
            // Forced literals are theory-consistent; record whether any
            // was uninterpreted for the backstop below, then validate
            // the model's disjunct choices in stage 2.
            LoopOutcome::Sat => self.theories.had_uninterpreted_atom(),
        };

        // ── Stage 2: validate the SAT model's chosen disjunct atoms ──
        //
        // The forced literals are consistent, but the SAT model also
        // committed truth values to the atoms *inside* disjunctions
        // (`(or (< x 0) (> x 0))` with `(= x 0)` picks one disjunct).
        // Those choices are not entailed, so a theory conflict among
        // them does NOT make the formula unsat — but it does mean THIS
        // boolean model is theory-infeasible, and we do not run the full
        // DPLL(T) refinement loop (theory conflict → learnt clause →
        // re-solve). So re-check the full model's atoms (each clause
        // atom at its model polarity) and, on a conflict, return
        // `Unknown` (→ theory/OxiZ delegation) rather than an unsound
        // `sat` — preserving soundness without the lazy-SMT machinery.
        self.theories.reset();
        let mut model_lits: Vec<(Term, bool)> = Vec::new();
        let mut seen: std::collections::HashSet<Term> = std::collections::HashSet::new();
        for clause in clauses {
            for lit in clause {
                if seen.insert(lit.atom.clone())
                    && let Some(&pol) = bool_assignment.get(&lit.atom.to_string())
                {
                    model_lits.push((lit.atom.clone(), pol));
                }
            }
        }
        match dpllt::run_once_with_deadline(&mut self.theories, &model_lits, deadline) {
            LoopOutcome::Sat => {
                // rc.32.x soundness backstop — even a theory-consistent
                // model is unsound to report as `Sat` if it rests on an
                // atom a sort-specialized theory could not interpret (a
                // nonlinear `(> (* x x) 0)`); UF then accepted it only as
                // an opaque boolean. Downgrade to `Unknown` so the
                // verdict is sound AND delegation (gated on `unknown`)
                // fires — rc.27 (S.1) `had_opaque` → `Unknown`, here
                // generalized from nested boolean structure to theory
                // atoms.
                if forced_uninterpreted || self.theories.had_uninterpreted_atom() {
                    // Plain detail — the CLI wraps it as the Verus-canonical
                    // `(incomplete …)` reason-unknown (do not pre-wrap here).
                    SatResult::Unknown {
                        reason: "native theory abstraction: a theory atom was \
                                 assigned without theory interpretation"
                            .to_string(),
                    }
                } else {
                    SatResult::Sat {
                        model: crate::result::Model::from_assignment(bool_assignment),
                    }
                }
            }
            LoopOutcome::Unsat { .. } => SatResult::Unknown {
                reason: "a satisfying boolean model was theory-infeasible and native \
                         DPLL(T) does not refine across theory conflicts"
                    .to_string(),
            },
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

/// rc.32.x — collect the literals **forced** to a definite truth value
/// by asserting `term` at `polarity`, pushing each as `(atom, polarity)`
/// into `out`. A conjunct of an asserted-true conjunction must hold in
/// every model, so it is forced; a disjunct of an asserted-true
/// disjunction is not. We descend through `not` (flipping polarity) and
/// the connectives whose forced structure is a conjunction —
/// asserted-true `and`, asserted-false `or` (`¬(A∨B) = ¬A ∧ ¬B`),
/// asserted-false `=>` (`¬(A⇒B) = A ∧ ¬B`) — and stop at a genuine
/// disjunction (asserted-true `or`/`=>`, asserted-false `and`), which
/// forces nothing. The leaves are the atomic theory literals the
/// theory layer must check; routing only these keeps the single-model
/// theory check sound for `unsat` (every routed literal is entailed).
fn collect_forced_literals(term: &Term, polarity: bool, out: &mut Vec<(Term, bool)>) {
    if let Some(inner) = term.dest_not() {
        collect_forced_literals(&inner, !polarity, out);
        return;
    }
    if polarity {
        if let Some((a, b)) = term.dest_and() {
            collect_forced_literals(&a, true, out);
            collect_forced_literals(&b, true, out);
            return;
        }
        if term.dest_or().is_some() || term.dest_imp().is_some() {
            return; // asserted-true disjunction — nothing forced
        }
    } else {
        if let Some((a, b)) = term.dest_or() {
            collect_forced_literals(&a, false, out);
            collect_forced_literals(&b, false, out);
            return;
        }
        if let Some((a, b)) = term.dest_imp() {
            collect_forced_literals(&a, true, out);
            collect_forced_literals(&b, false, out);
            return;
        }
        if term.dest_and().is_some() {
            return; // asserted-false conjunction — disjunctive, nothing forced
        }
    }
    out.push((term.clone(), polarity));
}

/// rc.30 (Y4) — decompose `App(App(…Const(name), a₁)…, aₙ)` into
/// `(name, [a₁, …, aₙ])`; a bare `Const(name)` yields `(name, [])`.
/// `None` for any other head shape.
fn decompose_app(t: &Term) -> Option<(String, Vec<Term>)> {
    let mut args: Vec<Term> = Vec::new();
    let mut cur = t.clone();
    loop {
        match cur.kind() {
            TermInner::App(f, x) => {
                args.push(x.clone());
                cur = f.clone();
            }
            TermInner::Const(c) => {
                args.reverse();
                return Some((c.name.clone(), args));
            }
            _ => return None,
        }
    }
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

    /// rc.30 (Y4) — the selector-normalization pass rewrites
    /// `value(Some_int_ x)` to `x`, so `value(Some_int_ x) ≠ x` is
    /// unsat end-to-end through the Solver.
    #[test]
    fn selector_normalization_makes_field_access_unsat() {
        use adsmt_theory::datatypes::DatatypeDecl;
        let opt = Type::const_("Option_int_", adsmt_core::Kind::Type);
        let int = Type::const_("Int", adsmt_core::Kind::Type);
        let mut s = Solver::new();
        s.declare_datatype(
            DatatypeDecl::inductive("Option_int_", vec!["None".into(), "Some_int_".into()])
                .with_selectors(vec![vec![], vec!["value".into()]]),
        );
        let some = Term::const_("Some_int_", Type::fun(int.clone(), opt).unwrap());
        let value = Term::var("value", Type::fun(opt_const(), int.clone()).unwrap());
        let x = Term::var("x", int);
        // value(Some_int_ x) ≠ x  → unsat (selector reduction)
        let some_x = Term::app(some, x.clone()).unwrap();
        let val = Term::app(value, some_x).unwrap();
        let eq = Term::mk_eq(val, x).unwrap();
        s.assert_negated(eq);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    fn opt_const() -> Type {
        Type::const_("Option_int_", adsmt_core::Kind::Type)
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

    // === rc.32.x — native theory-atom soundness (verus-fork P0) ===
    //
    // The native path used to abstract every arithmetic atom to a free
    // boolean (comparison atoms routed by their Bool result sort, never
    // reaching LinArith; conjuncts of an asserted `(and …)` never
    // surfaced to the theory check), so theory-`unsat` formulas returned
    // a confident, unsound `sat`. These pin the routing fix + LinArith
    // positive-equality + forced-literal decomposition + the two-stage
    // model validation + the uninterpreted-atom backstop.

    fn int_ty() -> Type { Type::const_("Int", adsmt_core::Kind::Type) }

    fn cmp(op: &str, lhs: Term, rhs: Term) -> Term {
        let int = int_ty();
        let opty = Type::fun(int.clone(), Type::fun(int, Type::bool_()).unwrap()).unwrap();
        let head = Term::const_(op, opty);
        Term::app(Term::app(head, lhs).unwrap(), rhs).unwrap()
    }

    fn int_lit(n: &str) -> Term { Term::const_(n, int_ty()) }

    #[test]
    fn theory_unsat_conjunction_is_not_sat() {
        // (and (> x 0) (< x 0)) — the verus-fork repro. Both conjuncts
        // are forced, route to LinArith, and conflict → unsat.
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        let gt = cmp(">", x.clone(), int_lit("0"));
        let lt = cmp("<", x, int_lit("0"));
        s.assert(Term::mk_and(gt, lt).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn numeral_equality_conflict_is_unsat() {
        // (and (= x 5) (= x 6)) — LinArith positive-equality turns each
        // into bounds; x ≥ 6 ∧ x ≤ 5 conflicts. (UF alone can't see that
        // 5 and 6 are distinct numerals, which is why this was `sat`.)
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        let e5 = Term::mk_eq(x.clone(), int_lit("5")).unwrap();
        let e6 = Term::mk_eq(x, int_lit("6")).unwrap();
        s.assert(Term::mk_and(e5, e6).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn single_comparison_is_sat() {
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        s.assert(cmp(">", x, int_lit("0")));
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
    }

    #[test]
    fn int_equality_is_sat_not_over_downgraded() {
        // (= x y) must stay a definite `Sat` — LinArith accepts the
        // equality (x − y ≤ 0 ∧ x − y ≥ 0); the backstop exempts
        // equality-shaped atoms, so this is not downgraded to Unknown.
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        s.assert(Term::mk_eq(x, y).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
    }

    #[test]
    fn satisfiable_arith_range_is_sat() {
        // (and (> x 0) (< x 10)) — both forced, consistent → sat.
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        let gt = cmp(">", x.clone(), int_lit("0"));
        let lt = cmp("<", x, int_lit("10"));
        s.assert(Term::mk_and(gt, lt).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
    }

    #[test]
    fn disjunctive_theory_conflict_is_never_sat() {
        // (or (< x 0) (> x 0)) ∧ (= x 0) is theory-UNSAT (0 is neither
        // < 0 nor > 0). The single-model native path can't refine across
        // the disjunct choice, but it must never return `sat`: the
        // two-stage model validation downgrades to Unknown (→ delegation).
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        let lt = cmp("<", x.clone(), int_lit("0"));
        let gt = cmp(">", x.clone(), int_lit("0"));
        s.assert(Term::mk_or(lt, gt).unwrap());
        s.assert(Term::mk_eq(x, int_lit("0")).unwrap());
        assert!(!matches!(s.check_sat(), SatResult::Sat { .. }));
    }

    #[test]
    fn nonlinear_atom_is_never_sat() {
        // (> (* x x) 0) — LinArith can't parse the nonlinear term, so it
        // `Ignored`s the atom; the backstop downgrades the would-be
        // free-boolean `sat` to Unknown rather than trusting it.
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        let int = int_ty();
        let mul = Term::const_(
            "*",
            Type::fun(int.clone(), Type::fun(int.clone(), int).unwrap()).unwrap(),
        );
        let xx = Term::app(Term::app(mul, x.clone()).unwrap(), x).unwrap();
        s.assert(cmp(">", xx, int_lit("0")));
        assert!(!matches!(s.check_sat(), SatResult::Sat { .. }));
    }

    #[test]
    fn boolean_disjunction_stays_sat() {
        // Pure-propositional disjunction has no theory atoms; the
        // backstop and the two-stage check leave it a definite `Sat`.
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(Term::mk_or(p, q).unwrap());
        assert!(matches!(s.check_sat(), SatResult::Sat { .. }));
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
    fn delegated_unsat_cert_records_assumptions_and_delegation_witness() {
        // rc.33 (Gap A): a cert synthesised for an externally-decided
        // (delegated) `unsat` records each assertion as an `Assume`,
        // closes with a Theory step over `false`, and carries the
        // `oxiz-delegation` opaque witness — so `--emit-cert*` covers
        // obligations only OxiZ can decide.
        let mut s = Solver::new();
        let x = Term::var("x", int_ty());
        s.assert(cmp(">", x.clone(), int_lit("0")));
        s.assert(cmp("<", x, int_lit("0")));
        let cert = s
            .build_delegated_unsat_cert("oxiz")
            .expect("proof mode default Always → Some cert");
        assert!(cert.steps.len() >= 3, "two assumes + a closing step");
        let final_step = &cert.steps[cert.conclusion.0 as usize];
        match &final_step.body {
            adsmt_cert::StepBody::Theory { name, witness, .. } => {
                assert_eq!(name, "delegation");
                assert!(
                    matches!(witness, adsmt_cert::witness::TheoryWitness::Opaque { kind, .. } if kind == "oxiz-delegation"),
                    "expected the oxiz-delegation opaque witness",
                );
            }
            other => panic!("expected a Theory closing step, got {other:?}"),
        }
        assert!(final_step.result.concl.is_false_const());
    }

    #[test]
    fn proof_mode_none_skips_delegated_cert() {
        let s = Solver::new().with_proof_mode(ProofMode::None);
        assert!(s.build_delegated_unsat_cert("oxiz").is_none());
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
        // UF congruence — falls through to `check_via_theories_with_model`
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

    // §3.5.F regression — guard-evaluation gate + event-replay
    // scan semantics.

    #[test]
    fn replay_returns_replayed_sat_on_empty_guard_set_and_empty_events() {
        let s = Solver::default();
        let trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        let outcome = s.replay_aot_cdcl_trace(&trace, &[]);
        match outcome {
            ReplayOutcome::Replayed { verdict: SatResult::Sat { .. } } => {}
            other => panic!("expected Replayed{{Sat}} on vacuous trace, got {other:?}"),
        }
    }

    #[test]
    fn replay_returns_guard_miss_on_failed_skeleton_guard() {
        let s = Solver::default();
        let mut trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        // Live skeleton is `SkeletonShape(0)` on a solver with
        // no assertions; a guard pinned to a non-zero hash misses.
        trace.guards.push(adsmt_jit::JitGuard::SkeletonShape(
            adsmt_jit::SkeletonShape(0xdead_beef),
        ));
        let outcome = s.replay_aot_cdcl_trace(&trace, &[]);
        assert!(matches!(outcome, ReplayOutcome::GuardMiss));
    }

    #[test]
    fn replay_returns_replayed_when_equiv_class_holds() {
        let s = Solver::default();
        let mut trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        trace.guards.push(adsmt_jit::JitGuard::EquivClass {
            a: "a".to_string(),
            b: "b".to_string(),
        });
        let classes = vec![("a".to_string(), 1), ("b".to_string(), 1)];
        let outcome = s.replay_aot_cdcl_trace(&trace, &classes);
        match outcome {
            ReplayOutcome::Replayed { verdict: SatResult::Sat { .. } } => {}
            other => panic!("expected Replayed{{Sat}}, got {other:?}"),
        }
    }

    #[test]
    fn replay_returns_replayed_unsat_when_conflict_event_present_and_no_restart() {
        let s = Solver::default();
        let mut trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        trace.events.push(adsmt_jit::CdclTraceEvent::Decide { atom: 1, polarity: true });
        trace.events.push(adsmt_jit::CdclTraceEvent::Conflict {
            learnt: vec![(1, false)],
            lbd: 1,
        });
        let outcome = s.replay_aot_cdcl_trace(&trace, &[]);
        match outcome {
            ReplayOutcome::Replayed { verdict: SatResult::Unsat { .. } } => {}
            other => panic!("expected Replayed{{Unsat}}, got {other:?}"),
        }
    }

    #[test]
    fn replay_returns_guards_passed_on_conflict_with_restart_followup() {
        // Restart after the conflict means the trace's final
        // verdict is no longer pinned — caller must fall through
        // to full CDCL.
        let s = Solver::default();
        let mut trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
        trace.events.push(adsmt_jit::CdclTraceEvent::Conflict {
            learnt: vec![(1, false)],
            lbd: 1,
        });
        trace.events.push(adsmt_jit::CdclTraceEvent::Restart);
        let outcome = s.replay_aot_cdcl_trace(&trace, &[]);
        assert!(matches!(outcome, ReplayOutcome::GuardsPassed));
    }

    // §1.1 / §1.2 — dump_cdcl_state + aot_cdcl_state cache.

    #[test]
    fn dump_cdcl_state_empty_solver_produces_empty_clauses_and_state() {
        let s = Solver::default();
        let (clauses, state, had_opaque) = s.dump_cdcl_state();
        assert!(clauses.is_empty());
        assert!(state.trail.is_empty());
        assert!(!had_opaque);
    }

    #[test]
    fn dump_cdcl_state_after_assert_propagates_unit() {
        // (assert p) → 1-literal clause → root-level trail entry.
        let mut s = Solver::default();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        let (clauses, state, had_opaque) = s.dump_cdcl_state();
        assert_eq!(clauses.len(), 1);
        assert_eq!(state.trail.len(), 1);
        assert_eq!(state.trail[0].atom, p);
        assert!(state.trail[0].polarity);
        assert!(!had_opaque);
    }

    #[test]
    fn aot_cdcl_state_returns_none_without_with_aot_cdcl() {
        let s = Solver::default();
        assert!(s.aot_cdcl_state().is_none());
    }

    #[test]
    fn start_take_jit_recording_round_trips() {
        let mut s = Solver::default();
        assert!(s.take_jit_recording().is_none());
        s.start_jit_recording();
        let drained = s.take_jit_recording().expect("recording was started");
        assert!(drained.is_empty());
    }

    // §3.2 — JIT registry integration.

    #[test]
    fn jit_registry_defaults_to_none() {
        let s = Solver::default();
        assert!(s.jit_registry().is_none());
    }

    #[test]
    fn jit_tracer_captures_propagate_events_on_sat_check() {
        // (assert p) + (assert (or p q)) → SAT.  The recording
        // cdcl variant should surface at least one Propagate
        // event for `p` along the way.
        let mut s = Solver::default();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(p);
        s.assert(Term::mk_or(
            Term::var("p", Type::bool_()),
            q,
        ).unwrap());
        s.start_jit_recording();
        let _ = s.check_sat();
        let tracer = s.take_jit_recording().expect("recording was started");
        assert!(
            !tracer.is_empty(),
            "tracer should record at least one propagate / decide event"
        );
        // At least one event should be a Propagate (root-level
        // unit-clause assignment for `p`).
        assert!(
            tracer
                .clone()
                .finalize(adsmt_jit::GF2Snapshot::empty(), vec![])
                .events
                .iter()
                .any(|e| matches!(e, adsmt_jit::CdclTraceEvent::Propagate { .. })),
            "tracer should record at least one Propagate event",
        );
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64"))]
    #[test]
    fn start_jit_caching_then_register_trace_returns_kernel_id() {
        let mut s = Solver::default();
        // Inactive registry — registration is a no-op.
        let trace = adsmt_jit::Trace::new(
            adsmt_jit::SkeletonShape(0xc0de),
            vec![],
            0,
        );
        let id_when_inactive = s.register_jit_trace(trace.clone()).unwrap();
        assert!(id_when_inactive.is_none());
        // Active registry — returns the assigned id.
        s.start_jit_caching();
        let id_when_active = s
            .register_jit_trace(trace)
            .expect("x86_64 noop emit must succeed");
        assert_eq!(id_when_active, Some(0));
        let registry = s.jit_registry().expect("registry was started");
        assert_eq!(registry.cached_traces(), 1);
        assert_eq!(registry.compiled_kernels(), 1);
    }

    // === rc.27 (S.1/S.3) — soundness: an opaque (un-flattenable)
    // assertion must never mask a contradiction into `sat` ===

    /// verus-fork rc.26 retry P0 reproducer: an OR-of-AND assert
    /// (`(=> P (and Q R))`, which the v0.3 CNF flattener returns
    /// `None` for) co-occurring with `(assert false)` must be
    /// `Unsat`, not `Sat`.  Pre-rc.27 the `None` arm abandoned the
    /// clause accumulator (empty clause included) and re-routed
    /// through the theory path, which ignores propositional
    /// `false` → unsound `sat`.
    #[test]
    fn opaque_assert_does_not_mask_false_into_sat() {
        let bool_ = Type::bool_();
        let p = Term::var("P", bool_.clone());
        let q = Term::var("Q", bool_.clone());
        let r = Term::var("R", bool_);
        // (=> P (and Q R)) — nested OR-of-AND, opaque to the flattener.
        let or_of_and = Term::mk_imp(
            p,
            Term::mk_and(q, r).unwrap(),
        )
        .unwrap();
        let mut s = Solver::new();
        s.assert(or_of_and);
        s.assert(Term::false_const());
        assert!(
            matches!(s.check_sat(), SatResult::Unsat { .. }),
            "asserting false alongside an opaque OR-of-AND must be unsat"
        );
    }

    /// rc.29 (S.2) — `(or P (and Q R))` was reported `Unknown` at
    /// rc.27 (sound but incomplete: the OR-of-AND was opaque to the
    /// flattener).  With the Tseitin transform it now flattens and
    /// the genuinely-satisfiable formula resolves to `Sat`
    /// (e.g. P = true).  This is the completeness win — what was
    /// `Unknown` is now the correct definite verdict.
    #[test]
    fn or_of_and_alone_is_sat_via_tseitin() {
        let bool_ = Type::bool_();
        let p = Term::var("P", bool_.clone());
        let q = Term::var("Q", bool_.clone());
        let r = Term::var("R", bool_);
        let or_of_and = Term::mk_or(p, Term::mk_and(q, r).unwrap()).unwrap();
        let mut s = Solver::new();
        s.assert(or_of_and);
        assert!(
            matches!(s.check_sat(), SatResult::Sat { .. }),
            "(or P (and Q R)) is satisfiable; Tseitin (S.2) resolves it to Sat, not Unknown"
        );
    }

    /// rc.29 (S.2) — the verus-fork canonical completeness witness:
    /// `(or (and P (not P)) (and P (not P)))` is structurally unsat
    /// (a contradiction buried inside an OR-of-AND with no companion
    /// flattenable `false`).  Pre-rc.29 this was `Unknown` (z3:
    /// `unsat`); the Tseitin aux makes the buried contradiction reach
    /// the SAT solve and resolve to `Unsat`.
    #[test]
    fn or_of_and_buried_contradiction_is_unsat() {
        let bool_ = Type::bool_();
        let p = Term::var("P", bool_);
        let pnp = || Term::mk_and(p.clone(), Term::mk_not(p.clone()).unwrap()).unwrap();
        let witness = Term::mk_or(pnp(), pnp()).unwrap();
        let mut s = Solver::new();
        s.assert(witness);
        assert!(
            matches!(s.check_sat(), SatResult::Unsat { .. }),
            "a contradiction buried in an OR-of-AND must resolve to Unsat via Tseitin (S.2)"
        );
    }

    /// Property-style guard: `false` asserted alongside an
    /// arbitrary (here: satisfiable, flattenable) prefix is unsat.
    #[test]
    fn false_alongside_satisfiable_prefix_is_unsat() {
        let bool_ = Type::bool_();
        let p = Term::var("P", bool_.clone());
        let q = Term::var("Q", bool_);
        let mut s = Solver::new();
        s.assert(Term::mk_or(p, q).unwrap()); // satisfiable
        s.assert(Term::false_const());
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    /// rc.28 (S.1-AOT) — the AOT-load analogue of
    /// `opaque_assert_does_not_mask_false_into_sat`.  A baked
    /// prelude whose flattenable subset contains the empty clause
    /// (the `(assert false)` / `(assert (not true))` contradiction)
    /// must reach the seeded CDCL solve and produce `Unsat` — the
    /// pre-rc.28 `restore_cdcl_state_into` swallowed the empty
    /// clause via a blanket `if !lits.is_empty()`, which is exactly
    /// the verus-fork-reported `sat`-for-unsat AOT soundness gap.
    #[test]
    fn restored_empty_clause_is_kept_and_yields_unsat() {
        // A baked section carrying a single *genuine* empty clause.
        let mut section = adsmt_aot::CdclSection::empty([0u8; 32], 0);
        section.clauses.push(adsmt_aot::CdclClause { lits: Vec::new() });
        let mut s = Solver::new();
        // No pool atoms needed — the empty clause references none.
        s.restore_cdcl_state_into(&section, &[]);
        assert_eq!(
            s.aot_prelude_clauses().len(),
            1,
            "the genuine empty clause must survive restore, not be dropped"
        );
        assert!(
            s.aot_prelude_clauses()[0].is_empty(),
            "the surviving clause is the empty (contradiction) clause"
        );
        // With the empty clause prepended, any check is unsat.
        assert!(
            matches!(s.check_sat(), SatResult::Unsat { .. }),
            "a baked empty clause must make --aot-load report unsat"
        );
    }

    /// rc.28 (S.1-AOT) — the AOT-load analogue of
    /// `opaque_assert_alone_is_unknown_not_sat`.  When the baked
    /// prelude dropped an opaque assertion (`had_opaque`), a later
    /// theory `Sat` on load must downgrade to `Unknown`, never
    /// `Sat` — mirroring the baseline `had_opaque` discipline.
    #[test]
    fn restored_had_opaque_downgrades_sat_to_unknown() {
        let mut section = adsmt_aot::CdclSection::empty([0u8; 32], 0);
        section.had_opaque = true; // bake-time dropped an opaque assert
        let mut s = Solver::new();
        s.restore_cdcl_state_into(&section, &[]);
        // No clauses, no contradiction — theory would say Sat, but
        // the opaque drop forces Unknown.
        assert!(
            matches!(s.check_sat(), SatResult::Unknown { .. }),
            "a baked opaque assertion must not be reported sat under --aot-load"
        );
    }
}
