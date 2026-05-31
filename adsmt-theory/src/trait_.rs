//! The [`Theory`] trait and supporting types.
//!
//! Every theory solver — UF, LIA, LRA, Arrays, Datatypes, and the
//! type-class theory (T_class) in `adsmt-class` — implements this
//! trait. Polite combination [`crate::polite`] then drives them in
//! lock-step through DPLL(T) and reconciles their cardinality
//! witnesses.

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{KernelError, KernelResult, Term, Type};

/// A ground literal: a Boolean-typed term plus a polarity.
#[derive(Clone, Debug)]
pub struct Literal {
    pub term: Term,
    pub polarity: bool,
}

impl Literal {
    pub fn positive(term: Term) -> KernelResult<Self> {
        Self::check_bool(&term)?;
        Ok(Literal { term, polarity: true })
    }

    pub fn negative(term: Term) -> KernelResult<Self> {
        Self::check_bool(&term)?;
        Ok(Literal { term, polarity: false })
    }

    pub fn negate(self) -> Self {
        Literal { term: self.term, polarity: !self.polarity }
    }

    fn check_bool(t: &Term) -> KernelResult<()> {
        if t.type_of() != Type::bool_() {
            return Err(KernelError::TypeMismatch {
                expected: "Bool".into(),
                found: t.type_of().to_string(),
            });
        }
        Ok(())
    }
}

/// Outcome of [`Theory::assert`].
#[derive(Clone, Debug)]
pub enum AssertResult {
    /// The theory accepted the literal into its state.
    Accepted,
    /// The literal is outside this theory's signature; ignored.
    Ignored,
    /// Asserting this literal immediately violates the theory.
    Conflict { witness: TheoryWitness },
}

/// Outcome of [`Theory::check`].
#[derive(Clone, Debug)]
pub enum CheckResult {
    /// State is consistent (as far as this theory can tell).
    Sat,
    /// State is inconsistent; witness explains the conflict.
    Unsat { witness: TheoryWitness },
    /// Theory cannot decide; abduction is the escalation.
    Unknown { reason: String },
}

/// A hypothesis that would let the theory prove a goal.
#[derive(Clone, Debug)]
pub struct AbductionCandidate {
    pub theory: &'static str,
    pub hypothesis: Term,
    pub explanation: Option<String>,
}

/// A theory solver participating in DPLL(T) and polite combination.
pub trait Theory: Send {
    /// Stable identifier — also used for theory ordering and certificate emission.
    fn name(&self) -> &'static str;

    /// Does this theory reason about literals over the given sort?
    fn handles_sort(&self, ty: &Type) -> bool;

    /// Add a ground literal to the theory's accumulated state.
    fn assert(&mut self, lit: Literal) -> AssertResult;

    /// Is the current state consistent?
    fn check(&mut self) -> CheckResult;

    /// Conflict witness if the most recent [`Self::check`] returned `Unsat`.
    /// Stateless theories may return `None` if they have not been
    /// checked since the last reset.
    fn explain(&self) -> Option<TheoryWitness>;

    /// Equalities derived from current state, to share with peer theories.
    fn derive_equalities(&self) -> Vec<(Term, Term)> { Vec::new() }

    /// Disequalities derived from current state, to share with peer theories.
    fn derive_disequalities(&self) -> Vec<(Term, Term)> { Vec::new() }

    /// Politeness witness for a sort: how many distinct elements can
    /// the theory accommodate? Return `None` for ω (stably infinite).
    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness;

    /// Abductive output: which hypotheses would make `goal` provable?
    /// Default: empty (theory does not contribute abductive candidates).
    fn abduce(&self, goal: &Literal) -> Vec<AbductionCandidate> {
        let _ = goal;
        Vec::new()
    }

    /// Push an incremental scope.
    fn push(&mut self) {}

    /// Pop one or more incremental scopes.
    fn pop(&mut self, levels: u32) { let _ = levels; }

    /// Drop all asserted state.
    fn reset(&mut self);

    /// Downcast hook — lets the engine reach the concrete theory
    /// type for theory-specific configuration (e.g. registering
    /// datatypes). Default returns `None`; concrete impls override.
    fn as_any_mut(&mut self) -> Option<&mut dyn std::any::Any> { None }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    #[test]
    fn positive_literal_requires_bool() {
        let p = Term::var("p", Type::bool_());
        assert!(Literal::positive(p).is_ok());
        let x = Term::var("x", Type::const_("Int", Kind::Type));
        assert!(Literal::positive(x).is_err());
    }

    #[test]
    fn negate_toggles_polarity() {
        let p = Term::var("p", Type::bool_());
        let lit = Literal::positive(p).unwrap();
        let neg = lit.negate();
        assert!(!neg.polarity);
    }
}
