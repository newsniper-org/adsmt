//! `Theory` trait + `Combination::register` integration.
//!
//! The §3.4 GF(2) Gröbner-basis decider is propositional, not
//! sort-specific.  That means a straight literal-level Theory
//! plugin can't observe the full clause set the F4 routine
//! needs — by the time `Theory::assert` fires on a literal,
//! CDCL has already CNF-flattened the formula and is feeding us
//! the per-decision atomic literals, not the original clauses.
//!
//! [`FiniteFieldTheory`] therefore plays a hybrid role:
//!
//! 1. It implements the standard `Theory` trait so it can sit in
//!    `Combination::register` alongside UF / Datatypes / Arith /
//!    Arrays / BV.  Its `assert` returns `AssertResult::Ignored`
//!    (the theory doesn't consume CDCL trail literals); its
//!    `check` honours the **periodic-interval** knob from the
//!    config — every `N` rounds it runs the F4 pass against the
//!    cached CNF clause set, returning `Unsat` on the GF(2)
//!    Hilbert-Weak-Nullstellensatz `1 ∈ basis` criterion.
//!
//! 2. The `Solver` integration code in `adsmt-engine` calls
//!    [`FiniteFieldTheory::install_dimacs_clauses`] before each
//!    `check_sat` to give the theory the CNF clause set, and
//!    [`FiniteFieldTheory::force_check`] from the
//!    **budget-exhaustion** path when the CDCL deadline elapses.
//!    Both knobs are independent ([`FiniteFieldConfig`]'s
//!    `periodic_interval` and `try_at_budget_exhaustion`).
//!
//! The split keeps the polite-combination invariants clean —
//! peer theories see `Ignored` on assert and the cardinality
//! reconciliation is unaffected — while still letting the
//! engine drive F4 at the granularity the verus-fork request
//! §3.4 cares about.

use std::any::Any;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::Type;
use adsmt_theory::trait_::{AssertResult, CheckResult, Literal, Theory};

use crate::bp_sat_encoder::decide_sat_via_f4;
use crate::sat_encoder::GroebnerSatVerdict;

/// Configuration for the GF(2) Gröbner theory plugin.
///
/// Both knobs are independent:
/// - `periodic_interval: 0` disables the periodic check;
///   any positive `N` runs an F4 pass every `N`-th call to
///   [`FiniteFieldTheory::check`].
/// - `try_at_budget_exhaustion: false` disables the
///   last-resort path; setting it `true` lets the engine
///   trigger one final F4 pass from
///   `Solver::check_sat_with_deadline` before returning
///   `Unknown`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteFieldConfig {
    /// Period (in theory-check rounds) at which to run the F4
    /// pass.  `0` disables periodic checks entirely.
    pub periodic_interval: usize,
    /// Whether the engine should call `force_check` once when
    /// CDCL's deadline elapses, before returning `Unknown`.
    pub try_at_budget_exhaustion: bool,
}

impl Default for FiniteFieldConfig {
    fn default() -> Self {
        Self {
            periodic_interval: 0,
            try_at_budget_exhaustion: false,
        }
    }
}

/// Theory plugin wrapping the GF(2) Gröbner-basis decider.
///
/// Created via [`FiniteFieldTheory::new`] and registered via
/// `Solver::with_finite_field(...)` from `adsmt-engine`.  The
/// engine installs the CNF clause set with
/// [`Self::install_dimacs_clauses`] before each `check_sat` and
/// optionally polls [`Self::force_check`] from the
/// budget-exhaustion path.
pub struct FiniteFieldTheory {
    config: FiniteFieldConfig,
    round_counter: u64,
    /// CNF clauses currently visible to this plugin; refreshed
    /// per-check_sat by the engine.  DIMACS shape: each clause is
    /// a `Vec<i32>`, `±` encodes literal polarity, `|i|` is the
    /// 1-based variable index.
    clauses: Vec<Vec<i32>>,
    /// Maximum variable index observed in `clauses`.
    n_vars: u32,
    /// Push/pop stack: `scope_versions[k]` is `clauses.len()` at
    /// the moment scope `k` was pushed, so `pop(1)` rolls
    /// `clauses` back to the previous state.
    scope_versions: Vec<usize>,
    /// Last conflict witness; reset on every `reset()`.
    conflict: Option<TheoryWitness>,
}

impl FiniteFieldTheory {
    /// Construct a fresh plugin with the given configuration.
    pub fn new(config: FiniteFieldConfig) -> Self {
        Self {
            config,
            round_counter: 0,
            clauses: Vec::new(),
            n_vars: 0,
            scope_versions: vec![0],
            conflict: None,
        }
    }

    /// Borrow the current configuration.
    pub fn config(&self) -> &FiniteFieldConfig {
        &self.config
    }

    /// Replace the configuration in-place.  Useful for
    /// re-tuning between `check_sat` calls; the round counter
    /// is *not* reset.
    pub fn set_config(&mut self, config: FiniteFieldConfig) {
        self.config = config;
    }

    /// Install the CNF clause set the engine will see during the
    /// next `check_sat`.  Called from
    /// `adsmt-engine::Solver::check_sat_with_deadline` at the
    /// start of every check; replaces any previously installed
    /// clause set wholesale.  The engine recomputes the full
    /// flattened CNF on every call, so this method's
    /// wholesale-replace semantics are intentional — the higher
    /// scope-version entries (set by intermediate `push()` calls)
    /// keep their `0` markers, and a subsequent `pop(N)`
    /// correctly truncates back to an empty clause set, which the
    /// next `check_sat` will re-install from whatever
    /// assertions survived the pop.
    pub fn install_dimacs_clauses(
        &mut self,
        clauses: Vec<Vec<i32>>,
        n_vars: u32,
    ) {
        self.clauses = clauses;
        self.n_vars = n_vars;
        // Re-stamp the base scope so subsequent push/pop tracks
        // the new clause-set length, not the old one.
        if self.scope_versions.is_empty() {
            self.scope_versions.push(self.clauses.len());
        } else {
            self.scope_versions[0] = self.clauses.len();
        }
    }

    /// Number of clauses currently installed.  Test-only
    /// observability hook.
    #[doc(hidden)]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Round counter — incremented on every `Theory::check` call.
    /// Test-only observability hook.
    #[doc(hidden)]
    pub fn round_counter(&self) -> u64 {
        self.round_counter
    }

    /// Run one F4 pass unconditionally, regardless of the
    /// periodic-interval setting.  Returns `Some(witness)` iff
    /// the constant `1` ends up in the Gröbner basis.  Called by
    /// the engine's budget-exhaustion hook when
    /// `try_at_budget_exhaustion` is on.
    pub fn force_check(&mut self) -> Option<TheoryWitness> {
        self.run_f4()
    }

    /// §3.5.E — return the current ideal's generator polynomials
    /// (one per installed CNF clause, plus the implicit
    /// `xᵢ² − xᵢ = 0` field equations the F4 / Buchberger
    /// kernel adds inside).  The §3.5.D `GF2Snapshot::capture`
    /// helper consumes this directly so the JIT recorder can
    /// snapshot the prelude's algebraic signature at trace
    /// boundary without running a fresh Gröbner computation.
    ///
    /// Returns an empty `Vec` when no DIMACS clauses have been
    /// installed yet — the bake-side recorder treats that as a
    /// degenerate (empty-ideal) signature.
    pub fn current_generators(&self) -> Vec<crate::polynomial::Polynomial> {
        crate::sat_encoder::cnf_to_generators(
            &self.clauses,
            self.n_vars as usize,
            crate::monomial::MonomialOrder::Grevlex,
        )
    }

    fn run_f4(&mut self) -> Option<TheoryWitness> {
        if self.clauses.is_empty() {
            return None;
        }
        match decide_sat_via_f4(&self.clauses, self.n_vars) {
            GroebnerSatVerdict::Unsat => {
                let w = TheoryWitness::Opaque {
                    kind: "FiniteField".into(),
                    notes: format!(
                        "GF(2) Gröbner basis contains the constant 1 \
                         (Hilbert Weak Nullstellensatz UNSAT) \
                         over {} variables / {} clauses",
                        self.n_vars,
                        self.clauses.len(),
                    ),
                };
                self.conflict = Some(w.clone());
                Some(w)
            }
            GroebnerSatVerdict::Sat => None,
        }
    }
}

impl Theory for FiniteFieldTheory {
    fn name(&self) -> &'static str {
        "FiniteField"
    }

    fn handles_sort(&self, ty: &Type) -> bool {
        ty == &Type::bool_()
    }

    /// The §3.4 plugin doesn't consume CDCL trail literals —
    /// CDCL has already CNF-flattened the formula by the time
    /// these arrive, so they tell us less than the full clause
    /// set the engine installs via `install_dimacs_clauses`.
    /// Returning `Ignored` keeps polite-combination peers
    /// (UF / Arith / Datatypes / Arrays / BV) free to track the
    /// same literal in their usual way.
    fn assert(&mut self, _lit: Literal) -> AssertResult {
        AssertResult::Ignored
    }

    fn check(&mut self) -> CheckResult {
        self.round_counter = self.round_counter.wrapping_add(1);
        if self.config.periodic_interval > 0
            && (self.round_counter
                % self.config.periodic_interval as u64)
                == 0
            && let Some(w) = self.run_f4()
        {
            return CheckResult::Unsat { witness: w };
        }
        CheckResult::Sat
    }

    fn explain(&self) -> Option<TheoryWitness> {
        self.conflict.clone()
    }

    fn cardinality_witness(&self, _sort: &Type) -> PoliteWitness {
        // Bool has at most 2 inhabitants (the verus-fork prelude
        // never asks the polite combination to reconcile this
        // sort against anything but Bool itself, but the value
        // is correct in case a future combination ever does).
        PoliteWitness {
            sort: "Bool".into(),
            upper_bound: Some(2),
        }
    }

    fn push(&mut self) {
        self.scope_versions.push(self.clauses.len());
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(v) = self.scope_versions.pop() {
                self.clauses.truncate(v);
            }
        }
        if self.scope_versions.is_empty() {
            self.scope_versions.push(0);
        }
    }

    fn reset(&mut self) {
        self.clauses.clear();
        self.n_vars = 0;
        self.scope_versions = vec![0];
        self.round_counter = 0;
        self.conflict = None;
    }

    fn as_any_mut(&mut self) -> Option<&mut dyn Any> {
        Some(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_config_is_fully_disabled() {
        let cfg = FiniteFieldConfig::default();
        assert_eq!(cfg.periodic_interval, 0);
        assert!(!cfg.try_at_budget_exhaustion);
    }

    #[test]
    fn assert_ignores_literal_per_design() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig::default());
        let p = adsmt_core::Term::var("p", adsmt_core::Type::bool_());
        let lit = Literal::positive(p).unwrap();
        let r = ff.assert(lit);
        assert!(matches!(r, AssertResult::Ignored));
    }

    #[test]
    fn check_without_clauses_returns_sat() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig {
            periodic_interval: 1,
            try_at_budget_exhaustion: false,
        });
        // periodic_interval = 1 → fires every round, but no
        // clauses installed → returns Sat trivially.
        assert!(matches!(ff.check(), CheckResult::Sat));
    }

    #[test]
    fn force_check_returns_unsat_witness_on_polarity_contradiction() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig::default());
        // DIMACS encoding of `(x) ∧ (¬x)` — the smallest UNSAT.
        ff.install_dimacs_clauses(vec![vec![1], vec![-1]], 1);
        let w = ff.force_check().expect("expected Unsat witness");
        match w {
            TheoryWitness::Opaque { kind, .. } => {
                assert_eq!(kind, "FiniteField");
            }
            _ => panic!("expected Opaque variant"),
        }
    }

    #[test]
    fn periodic_check_fires_at_configured_interval() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig {
            periodic_interval: 3,
            try_at_budget_exhaustion: false,
        });
        // Install a known-Unsat clause set so when the period
        // fires we expect a conflict witness.
        ff.install_dimacs_clauses(vec![vec![1], vec![-1]], 1);
        // Rounds 1, 2 → Sat (periodic interval not reached).
        assert!(matches!(ff.check(), CheckResult::Sat));
        assert!(matches!(ff.check(), CheckResult::Sat));
        // Round 3 → matches periodic_interval → runs F4 → Unsat.
        let r = ff.check();
        match r {
            CheckResult::Unsat { .. } => {}
            other => panic!("expected Unsat on periodic round, got {other:?}"),
        }
    }

    #[test]
    fn periodic_zero_never_runs_f4() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig {
            periodic_interval: 0,
            try_at_budget_exhaustion: false,
        });
        ff.install_dimacs_clauses(vec![vec![1], vec![-1]], 1);
        for _ in 0..1000 {
            assert!(matches!(ff.check(), CheckResult::Sat));
        }
        // Counter still increments so callers polling it from
        // outside can observe the round count.
        assert_eq!(ff.round_counter(), 1000);
    }

    #[test]
    fn push_pop_restores_clause_set() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig::default());
        ff.install_dimacs_clauses(vec![vec![1]], 1);
        ff.push();
        // Simulate the engine appending a clause under the
        // pushed scope.  install replaces wholesale so we use a
        // synthetic append for the test.
        ff.clauses.push(vec![-1]);
        assert_eq!(ff.clause_count(), 2);
        ff.pop(1);
        assert_eq!(ff.clause_count(), 1);
    }

    #[test]
    fn reset_drops_state() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig {
            periodic_interval: 2,
            try_at_budget_exhaustion: true,
        });
        ff.install_dimacs_clauses(vec![vec![1], vec![-1]], 1);
        let _ = ff.check();
        let _ = ff.force_check();
        assert!(ff.explain().is_some());
        ff.reset();
        assert_eq!(ff.clause_count(), 0);
        assert_eq!(ff.round_counter(), 0);
        assert!(ff.explain().is_none());
        // Config persists across reset (matches the convention
        // for other theory plugins).
        assert_eq!(ff.config().periodic_interval, 2);
    }

    #[test]
    fn handles_sort_recognises_bool_only() {
        let ff = FiniteFieldTheory::new(FiniteFieldConfig::default());
        assert!(ff.handles_sort(&adsmt_core::Type::bool_()));
        let int_ = adsmt_core::Type::const_("Int", adsmt_core::Kind::Type);
        assert!(!ff.handles_sort(&int_));
    }

    #[test]
    fn as_any_mut_enables_engine_downcast() {
        let mut ff = FiniteFieldTheory::new(FiniteFieldConfig::default());
        let any = ff.as_any_mut().expect("as_any_mut returns Some");
        let _ff_back = any
            .downcast_mut::<FiniteFieldTheory>()
            .expect("downcast back to FiniteFieldTheory");
    }
}
