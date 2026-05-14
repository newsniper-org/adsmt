//! Theory and instance witnesses carried by certificate steps.
//!
//! These types pin down the *shape* of each theory's witness so a
//! checker can re-verify the theory step. v0.1 includes structural
//! skeletons for the theories planned through v0.5; theories not yet
//! shipped use the `Opaque` placeholder.

use adsmt_core::Term;

use crate::canonical::StepId;

/// Witness accompanying a `Theory` step.
#[derive(Clone, Debug)]
pub enum TheoryWitness {
    /// Equality reasoning via congruence and transitivity.
    Euf(EufWitness),
    /// Farkas-style witness for LIA / LRA.
    LinArith(LinArithWitness),
    /// Read-over-write reasoning for the theory of arrays.
    Arrays(ArrayWitness),
    /// Datatype constructor disjointness / injectivity / acyclicity.
    Datatypes(DatatypeWitness),
    /// Cardinality reconciliation under polite combination.
    Polite(PoliteWitness),
    /// SAT-level DRAT proof: the clauses are the input encoded as
    /// i32 DIMACS literals, and `proof` is a sequence of
    /// RUP-derivable steps ending in the empty clause. v0.15
    /// upgrade over `Opaque` for Boolean-prop SAT verdicts.
    ///
    /// `dimacs_bytes` carries the same proof serialized to the
    /// canonical DIMACS-style DRAT byte format (populated by
    /// `adsmt-engine::oxiz_drat::emit_via_oxiz_writer` when the
    /// `oxiz` feature is enabled). Empty when the feature is off.
    ///
    /// `alethe_bytes` / `lfsc_bytes` / `coq_bytes` carry the same
    /// SAT-level unsat verdict serialized via `oxiz-proof`'s
    /// `AletheProof::write` / `LfscProof::write` / `CoqExporter`
    /// (populated by `adsmt-engine::oxiz_proof_emit` when the
    /// `oxiz-proof` feature is enabled). Empty when the feature is
    /// off.
    Drat {
        clauses: Vec<Vec<i32>>,
        proof: crate::drat::DratProof,
        dimacs_bytes: Vec<u8>,
        alethe_bytes: Vec<u8>,
        lfsc_bytes: Vec<u8>,
        coq_bytes: Vec<u8>,
    },
    /// Placeholder for theories whose witness format is not yet pinned
    /// down (e.g. BV/FP/Strings in pre-v0.5 development).
    Opaque { kind: String, notes: String },
}

/// Congruence-closure witness.
#[derive(Clone, Debug)]
pub struct EufWitness {
    pub steps: Vec<EufStep>,
}

#[derive(Clone, Debug)]
pub enum EufStep {
    /// `t = t` is built in.
    Reflexivity(Term),
    /// An equality drawn from hypotheses or earlier deductions.
    Hypothesis(Term),
    /// `f(s_1, …, s_n) = f(t_1, …, t_n)` from `s_i = t_i`.
    Congruence { head: Term, subs: Vec<EufStep> },
    /// `s = u` from `s = t` and `t = u`.
    Transitive(Box<EufStep>, Box<EufStep>),
    /// `t = s` from `s = t`.
    Symmetric(Box<EufStep>),
}

/// Farkas-style witness for linear arithmetic.
#[derive(Clone, Debug)]
pub struct LinArithWitness {
    pub bounds: Vec<LinearBound>,
    /// Nonnegative multipliers; their dot product with `bounds` must
    /// produce an evidently false bound.
    pub farkas: Vec<i64>,
}

#[derive(Clone, Debug)]
pub struct LinearBound {
    pub coeffs: Vec<(String, i64)>,
    pub op: BoundOp,
    pub rhs: i64,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BoundOp { Le, Lt, Eq, Ne, Ge, Gt }

#[derive(Clone, Debug)]
pub struct ArrayWitness {
    pub chain: Vec<ArrayStep>,
}

#[derive(Clone, Debug)]
pub enum ArrayStep {
    /// `select(a, i)` term.
    Select { array: Term, index: Term },
    /// `select(store(a, i, v), j)` resolves: same index ⇒ `v`,
    /// otherwise `select(a, j)`.
    ReadOverWrite {
        array: Term,
        write_index: Term,
        write_value: Term,
        read_index: Term,
        indices_equal: bool,
    },
    /// Extensionality witness term.
    Extensionality(Term),
}

#[derive(Clone, Debug)]
pub struct DatatypeWitness {
    pub kind: DatatypeReason,
    pub constructors: Vec<String>,
    pub focused: Option<Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DatatypeReason {
    /// `C_i(...) ≠ C_j(...)` for distinct constructors.
    Disjointness,
    /// `C(a) = C(b)  ⟹  a = b`.
    Injectivity,
    /// `x ≠ Cons(_, x)` and similar.
    Acyclicity,
    /// `x = C_1(...) ∨ … ∨ x = C_n(...)`.
    CaseSplit,
}

/// Polite combination cardinality witness.
#[derive(Clone, Debug)]
pub struct PoliteWitness {
    pub sort: String,
    /// `None` means ω (stably infinite).
    pub upper_bound: Option<u64>,
}

/// Type-class instance resolution witness.
#[derive(Clone, Debug)]
pub struct InstanceWitness {
    /// Constant name from the instance database, e.g. `Functor_List`.
    pub instance_id: String,
    /// Sub-proofs for conditional instance premises.
    pub sub_proofs: Vec<StepId>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_witness_is_simple() {
        let w = TheoryWitness::Opaque {
            kind: "BV".into(),
            notes: "bit-blasting not yet implemented".into(),
        };
        if let TheoryWitness::Opaque { kind, .. } = w {
            assert_eq!(kind, "BV");
        } else {
            panic!("expected opaque");
        }
    }

    #[test]
    fn polite_omega_marker() {
        let p = PoliteWitness { sort: "Int".into(), upper_bound: None };
        assert!(p.upper_bound.is_none());
    }
}
