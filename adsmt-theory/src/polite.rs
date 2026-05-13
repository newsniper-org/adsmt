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
use adsmt_core::Type;

use crate::trait_::{CheckResult, Literal, Theory};

/// A registry of theories participating in combination.
pub struct Combination {
    theories: Vec<Box<dyn Theory>>,
}

impl Default for Combination {
    fn default() -> Self { Self { theories: Vec::new() } }
}

impl Combination {
    pub fn new() -> Self { Self::default() }

    pub fn register(&mut self, t: Box<dyn Theory>) {
        self.theories.push(t);
    }

    pub fn theories(&self) -> &[Box<dyn Theory>] { &self.theories }
    pub fn theories_mut(&mut self) -> &mut [Box<dyn Theory>] { &mut self.theories }

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

    /// Run `check` on each theory and return the first conflict, if any.
    pub fn check(&mut self) -> CombinedCheck {
        for t in &mut self.theories {
            match t.check() {
                CheckResult::Sat => continue,
                CheckResult::Unsat { witness } => {
                    return CombinedCheck::Unsat {
                        theory: t.name().to_string(),
                        witness,
                    };
                }
                CheckResult::Unknown { reason } => {
                    return CombinedCheck::Unknown {
                        theory: t.name().to_string(),
                        reason,
                    };
                }
            }
        }
        CombinedCheck::Sat
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
}
