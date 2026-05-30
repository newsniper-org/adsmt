//! v0.23 23A.3 — certificate format surface audit.
//!
//! Phase 1 freeze enforcement. Pins:
//! 1. `StepBody`'s 12 inference-rule variants — the v1.0 cert
//!    AST surface.
//! 2. `StepPattern`'s 6 closed variants — classical-axiom
//!    marker pattern surface.
//! 3. Public signatures of the per-ITP emit functions.

use adsmt_cert::canonical::{
    Certificate, StepBody, StepId, StepPattern,
};
use adsmt_cert::lean_emit::{emit_lean, try_emit_lean};
use adsmt_cert::prover_emit::lfsc_parse::{
    parse_document, render_isabelle, render_lean, render_rocq,
    LfscDocument,
};
use adsmt_core::Term;

const FROZEN_STEPBODY: &[&str] = &[
    "Assume", "Refl", "Trans", "Abs", "Beta", "EqMp",
    "Deduct", "Inst", "InstType", "Theory", "Instance", "Assumed",
];

const FROZEN_STEPPATTERN: &[&str] = &[
    "Theory", "Kind", "IdRange", "And", "Or", "Not",
];

#[test]
fn stepbody_variant_count_is_frozen() {
    assert_eq!(FROZEN_STEPBODY.len(), 12);
}

#[test]
fn steppattern_variant_count_is_frozen() {
    assert_eq!(FROZEN_STEPPATTERN.len(), 6);
}

fn body_variant_name(b: &StepBody) -> &'static str {
    match b {
        StepBody::Assume(_) => "Assume",
        StepBody::Refl(_) => "Refl",
        StepBody::Trans { .. } => "Trans",
        StepBody::Abs { .. } => "Abs",
        StepBody::Beta { .. } => "Beta",
        StepBody::EqMp { .. } => "EqMp",
        StepBody::Deduct { .. } => "Deduct",
        StepBody::Inst { .. } => "Inst",
        StepBody::InstType { .. } => "InstType",
        StepBody::Theory { .. } => "Theory",
        StepBody::Instance { .. } => "Instance",
        StepBody::Assumed { .. } => "Assumed",
    }
}

fn pattern_variant_name(p: &StepPattern) -> &'static str {
    match p {
        StepPattern::Theory(_) => "Theory",
        StepPattern::Kind(_) => "Kind",
        StepPattern::IdRange { .. } => "IdRange",
        StepPattern::And(_) => "And",
        StepPattern::Or(_) => "Or",
        StepPattern::Not(_) => "Not",
    }
}

#[test]
fn stepbody_assume_variant_is_recognisable() {
    let p = Term::var("p", adsmt_core::Type::bool_());
    let body = StepBody::Assume(p);
    assert_eq!(body_variant_name(&body), "Assume");
}

#[test]
fn steppattern_helper_constructors_produce_the_documented_shapes() {
    // The derived helpers xor / at_most_one / exactly_one are
    // sugar over And/Or/Not. The freeze pins the helpers'
    // existence by call-site availability — if they were removed,
    // this test wouldn't compile.
    let a = StepPattern::Theory("A".to_string());
    let b = StepPattern::Theory("B".to_string());
    let _xor = StepPattern::xor(a.clone(), b.clone());
    let _at_most_one = StepPattern::at_most_one(vec![a.clone(), b.clone()]);
    let _exactly_one = StepPattern::exactly_one(vec![a, b]);
    // Touch the variant-name helper so the compiler doesn't
    // dead-strip it; functionally a no-op.
    let leaf = StepPattern::Theory("dummy".into());
    assert_eq!(pattern_variant_name(&leaf), "Theory");
}

#[test]
fn per_itp_emit_signatures_compile() {
    // The freeze locks the *call signatures*. If any of these
    // emit functions changed its signature, the file wouldn't
    // type-check. Body content is governed by
    // `prover_emit_policy.md`.
    let cert = Certificate {
        steps: vec![],
        conclusion: StepId(0),
        mid_blocks: vec![],
        pattern_markers: vec![],
    };
    let _: String = emit_lean(&cert);
    let _: Result<String, _> = try_emit_lean(&cert);

    let doc: LfscDocument = parse_document("").unwrap();
    let _: String = render_lean(&doc);
    let _: String = render_rocq(&doc);
    let _: String = render_isabelle(&doc);
}
