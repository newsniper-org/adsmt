//! Cross-tool sanity check via `adsmt-cert::oxiz_drat_bridge` (P4).
//!
//! Engine-side anchor for the option-C cert ⇄ oxiz-proof bridge.
//! Pulls a DRAT proof out of a [`Certificate`]'s SAT-level
//! `TheoryWitness::Drat`, converts it via the rich bridge into an
//! `oxiz_proof::Proof` graph, converts back, and asserts the
//! round-trip is lossless (step shape and order preserved).
//!
//! The check is feature-gated on `oxiz-proof`; without the feature
//! the helper returns `RoundTripStatus::FeatureOff` so callers can
//! still link.

use adsmt_cert::Certificate;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoundTripStatus {
    /// Round-trip succeeded; cert's DRAT proof and the recovered
    /// proof have identical step shape and ordering.
    Lossless,
    /// Round-trip ran but step count or shape diverged.
    Diverged { reason: String },
    /// The certificate's final theory step did not carry a DRAT
    /// witness (theory unsat or non-SAT verdict).
    NoDratWitness,
    /// `oxiz-proof` feature is off so the rich bridge cannot run.
    FeatureOff,
}

/// Round-trip the SAT-level DRAT proof of `cert` through
/// `oxiz_proof::Proof` and report whether the recovered proof
/// matches the original step-for-step.
#[cfg(feature = "oxiz-proof")]
pub fn round_trip_check(cert: &Certificate) -> RoundTripStatus {
    use adsmt_cert::oxiz_drat_bridge::bridge::{
        from_oxiz_proof_rich, to_oxiz_proof_rich, BridgeMetadata,
    };
    use adsmt_cert::witness::TheoryWitness;
    use adsmt_cert::StepBody;

    let final_step = match cert.steps.get(cert.conclusion.0 as usize) {
        Some(s) => s,
        None => return RoundTripStatus::NoDratWitness,
    };
    let drat = match &final_step.body {
        StepBody::Theory {
            witness: TheoryWitness::Drat { proof, .. },
            ..
        } => proof,
        _ => return RoundTripStatus::NoDratWitness,
    };

    let meta = BridgeMetadata::fresh_for(drat);
    let (graph, _) = to_oxiz_proof_rich(drat, Some(&meta));
    let (recovered, recovered_meta) = from_oxiz_proof_rich(&graph);

    if recovered.steps.len() != drat.steps.len() {
        return RoundTripStatus::Diverged {
            reason: format!(
                "step count diverged: {} → {}",
                drat.steps.len(),
                recovered.steps.len(),
            ),
        };
    }
    for (i, (a, b)) in drat.steps.iter().zip(recovered.steps.iter()).enumerate() {
        use adsmt_cert::drat::DratStep;
        let same = matches!(
            (a, b),
            (DratStep::Add(x), DratStep::Add(y)) | (DratStep::Delete(x), DratStep::Delete(y))
                if x == y
        );
        if !same {
            return RoundTripStatus::Diverged {
                reason: format!("step {i} diverged after round-trip"),
            };
        }
    }
    if recovered_meta.clause_ids.len() != drat.steps.len() {
        return RoundTripStatus::Diverged {
            reason: "clause_ids length differs from step count".into(),
        };
    }
    RoundTripStatus::Lossless
}

#[cfg(not(feature = "oxiz-proof"))]
pub fn round_trip_check(_cert: &Certificate) -> RoundTripStatus {
    RoundTripStatus::FeatureOff
}

#[cfg(all(test, feature = "oxiz-proof"))]
mod tests {
    use super::*;
    use crate::result::SatResult;
    use crate::Solver;
    use adsmt_core::{Term, Type};

    #[test]
    fn polarity_contradiction_round_trips_losslessly() {
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
        assert_eq!(round_trip_check(&cert), RoundTripStatus::Lossless);
    }

    #[test]
    fn three_clause_unsat_round_trips_losslessly() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(Term::mk_or(p.clone(), q.clone()).unwrap());
        s.assert(Term::mk_not(p).unwrap());
        s.assert(Term::mk_not(q).unwrap());
        let SatResult::Unsat {
            certificate: Some(cert),
        } = s.check_sat()
        else {
            panic!("expected Unsat with cert");
        };
        assert_eq!(round_trip_check(&cert), RoundTripStatus::Lossless);
    }
}
