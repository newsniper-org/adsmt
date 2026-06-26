
//! Runtime audit library for adsmt certificate hygiene checks.
//!
//! # Why this crate exists
//!
//! Per the "Classical axiom imports (on-demand)" policy
//! (`prover_emit_policy.md` § "Pattern markers (cross-cutting)"),
//! cert producers can attach [`PatternMarker`]s that apply
//! classical-axiom markers to any step matching a
//! [`StepPattern`](adsmt_cert::StepPattern). A pattern that matches zero steps in the
//! actual cert is a *dead pattern* — almost certainly a producer
//! mistake (typo, forgotten filter, stale copy-paste) that wants
//! a warning.
//!
//! Dead-pattern detection is fundamentally a **runtime** check:
//! the cert is a dynamic object built by the solver in response
//! to whatever SMT problem was submitted. Compile-time tools
//! (rustc, clippy, dylint) have access to the source code where
//! [`PatternMarker`]s are *declared* but not to the cert they're
//! evaluated against. Only runtime entities that hold both the
//! cert and the markers can perform the actual audit.
//!
//! This crate provides that runtime audit:
//!
//! - [`dead_pattern_audit`] walks every [`PatternMarker`] in a
//!   cert and reports the ones that matched zero steps.
//! - [`DeadPatternDiagnostic`] carries the per-violation payload
//!   in a shape that's `serde::Serialize` for IDE consumption.
//! - [`diagnostics_to_json`] renders a diagnostic vector as a
//!   versioned JSON document VS Code (or any other diagnostic-
//!   consuming tool) can parse and display as squiggles.
//!
//! # Subjects (who calls this)
//!
//! - **Cert producer code** (right after building the cert).
//! - **Cert consumer / emitter** (`emit_lean`, `emit_rocq`,
//!   `emit_isabelle` can run the audit as a sibling check).
//! - **Test code** in cert-producer crates.
//! - **Separate audit binaries** (e.g., `adsmt-cli audit foo.smt2`).
//!
//! All four are runtime entities. None of them need nightly Rust,
//! cargo-dylint, or rustc internals.

use adsmt_cert::{Certificate, PatternMarker, SourceLoc, StepId};
use serde::Serialize;
use thiserror::Error;

/// Versioned JSON schema for the diagnostic output stream.
/// Bumped on backwards-incompatible additions; consumers should
/// reject unknown versions.
pub const JSON_SCHEMA_VERSION: u32 = 1;

/// Severity classification for [`DeadPatternDiagnostic`]. Today
/// only `Warning` is used; reserved for future "info" /
/// "deny-on-strict" variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Info,
    Warning,
    Error,
}

/// One dead-pattern diagnostic — emitted for each
/// [`PatternMarker`] in the cert whose pattern matched zero
/// steps.
#[derive(Clone, Debug, Serialize)]
pub struct DeadPatternDiagnostic {
    /// Index of the offending marker in `cert.pattern_markers`.
    /// Lets editors/tools cross-reference without parsing the
    /// pattern back out of the message.
    pub marker_index: usize,
    /// Optional human-readable name copied from the marker's
    /// `name` field (when populated by the cert producer).
    pub marker_name: Option<String>,
    /// Severity — `Warning` for v0.18.
    pub severity: Severity,
    /// Human-readable message ready for direct display.
    pub message: String,
    /// Optional source location copied from the marker's
    /// `source_loc` field. When `Some(...)` the diagnostic
    /// renders as an editor squiggle at the exact position.
    pub source_loc: Option<SourceLocPayload>,
    /// Total number of steps in the cert. Lets IDE consumers
    /// confirm the cert wasn't empty (which would dead-pattern
    /// every marker trivially).
    pub cert_step_count: usize,
    /// Steps that DID match other markers, useful for "why
    /// didn't mine match?" debugging. Empty when no other
    /// markers exist.
    pub steps_matched_by_siblings: Vec<StepIdPayload>,
}

/// Wire-format payload for [`SourceLoc`] — kept separate from
/// `adsmt_cert`'s struct so `adsmt-cert` doesn't have to depend
/// on `serde` itself.
#[derive(Clone, Debug, Serialize)]
pub struct SourceLocPayload {
    pub line: u32,
    pub column: u32,
}

impl From<SourceLoc> for SourceLocPayload {
    fn from(loc: SourceLoc) -> Self {
        Self { line: loc.line, column: loc.column }
    }
}

/// Wire-format payload for [`StepId`].
#[derive(Clone, Copy, Debug, Serialize)]
pub struct StepIdPayload {
    pub id: u32,
}

impl From<StepId> for StepIdPayload {
    fn from(id: StepId) -> Self {
        Self { id: id.0 }
    }
}

/// Top-level JSON document shape returned by
/// [`diagnostics_to_json`]. Versioned for forward compatibility.
#[derive(Clone, Debug, Serialize)]
pub struct DiagnosticsDocument {
    pub schema_version: u32,
    pub generator: &'static str,
    pub diagnostics: Vec<DeadPatternDiagnostic>,
}

#[derive(Debug, Error)]
pub enum AuditError {
    #[error("serialisation error: {0}")]
    Json(#[from] serde_json::Error),
}

/// Walk every [`PatternMarker`] in `cert` and report the ones
/// that matched zero steps.
///
/// # Algorithm
///
/// For each `(idx, marker)` pair in `cert.pattern_markers`:
///
/// 1. Iterate `cert.steps` and count how many match
///    `marker.pattern`.
/// 2. If the count is zero, build a [`DeadPatternDiagnostic`]
///    with the marker's metadata + the global cert step count +
///    optionally the steps matched by *sibling* markers (an
///    aid for "why didn't mine match while others did?").
///
/// Returns an empty vector when no markers are dead.
///
/// O(P × S) in the number of patterns × cert steps; pattern
/// matching itself is O(d) in pattern depth (And / Or / Not
/// recursion). For typical cert sizes this is well under a
/// millisecond.
pub fn dead_pattern_audit(cert: &Certificate) -> Vec<DeadPatternDiagnostic> {
    let mut out = Vec::new();
    for (idx, marker) in cert.pattern_markers.iter().enumerate() {
        if marker_is_live(marker, cert) {
            continue;
        }
        let matched_by_siblings: Vec<StepIdPayload> = cert
            .steps
            .iter()
            .filter(|step| {
                cert.pattern_markers
                    .iter()
                    .enumerate()
                    .any(|(other_idx, other)| {
                        other_idx != idx && other.pattern.matches(step)
                    })
            })
            .map(|step| step.id.into())
            .collect();
        out.push(DeadPatternDiagnostic {
            marker_index: idx,
            marker_name: marker.name.clone(),
            severity: Severity::Warning,
            message: format!(
                "pattern marker #{idx}{name} matched 0 of {total} cert steps",
                name = marker
                    .name
                    .as_deref()
                    .map(|n| format!(" (`{n}`)"))
                    .unwrap_or_default(),
                total = cert.steps.len(),
            ),
            source_loc: marker.source_loc.map(SourceLocPayload::from),
            cert_step_count: cert.steps.len(),
            steps_matched_by_siblings: matched_by_siblings,
        });
    }
    out
}

fn marker_is_live(marker: &PatternMarker, cert: &Certificate) -> bool {
    cert.steps.iter().any(|step| marker.pattern.matches(step))
}

/// Render a diagnostic vector as a versioned JSON document
/// suitable for IDE consumption (VS Code, etc.).
///
/// The JSON shape is versioned ([`JSON_SCHEMA_VERSION`]) and
/// stable within a major version. Editors should:
///
/// 1. Parse the top-level `schema_version` first and reject
///    unknown versions.
/// 2. Walk `diagnostics[]` and render each entry as a problem
///    with the supplied `severity`, `message`, and
///    `source_loc` (file path is omitted — editors that need
///    one populate it from their invocation context).
///
/// The output uses pretty-printed JSON for human readability;
/// `diagnostics_to_json_compact` is the dense alternative for
/// stream-consumption.
pub fn diagnostics_to_json(
    diagnostics: &[DeadPatternDiagnostic],
) -> Result<String, AuditError> {
    let document = DiagnosticsDocument {
        schema_version: JSON_SCHEMA_VERSION,
        generator: concat!("adsmt-lints v", env!("CARGO_PKG_VERSION")),
        diagnostics: diagnostics.to_vec(),
    };
    Ok(serde_json::to_string_pretty(&document)?)
}

/// Compact one-line JSON, suitable for log streams or
/// `--message-format=json` style pipelines.
pub fn diagnostics_to_json_compact(
    diagnostics: &[DeadPatternDiagnostic],
) -> Result<String, AuditError> {
    let document = DiagnosticsDocument {
        schema_version: JSON_SCHEMA_VERSION,
        generator: concat!("adsmt-lints v", env!("CARGO_PKG_VERSION")),
        diagnostics: diagnostics.to_vec(),
    };
    Ok(serde_json::to_string(&document)?)
}

/// Convenience for the most common workflow: audit a cert and
/// produce the JSON document in one call. Useful for separate
/// audit binaries / IDE extensions.
pub fn audit_to_json(cert: &Certificate) -> Result<String, AuditError> {
    diagnostics_to_json(&dead_pattern_audit(cert))
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cert::{
        canonical::CertBuilder, recorder::recorder as r,
        ClassicalMarkerSet, ClassicalModuleFamily, ClassicalSet, PatternMarker,
        StepKindTag, StepPattern,
    };
    use adsmt_core::{Term, Type};

    fn p() -> Term { Term::var("p", Type::bool_()) }

    fn empty_marker_set() -> ClassicalMarkerSet {
        ClassicalMarkerSet::empty()
    }

    fn refl_marker_set() -> ClassicalMarkerSet {
        ClassicalMarkerSet {
            should: ClassicalSet::from_iter([
                ClassicalModuleFamily::Propositional,
            ]),
            allow: vec![],
        }
    }

    fn build_cert_with_one_refl() -> adsmt_cert::Certificate {
        let mut b = CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        b.snapshot(h.step())
    }

    #[test]
    fn audit_empty_cert_with_no_markers_returns_empty() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        assert!(dead_pattern_audit(&cert).is_empty());
    }

    #[test]
    fn audit_finds_dead_pattern() {
        let mut b = CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        // Add a marker for Theory steps — the cert has only one
        // Refl step, so the marker matches zero.
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Theory),
            local_markers: refl_marker_set(),
            name: Some("theory_only_marker".into()),
            source_loc: None,
        });
        let cert = b.snapshot(h.step());
        let diags = dead_pattern_audit(&cert);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].marker_index, 0);
        assert_eq!(diags[0].marker_name.as_deref(), Some("theory_only_marker"));
        assert_eq!(diags[0].severity, Severity::Warning);
        assert_eq!(diags[0].cert_step_count, 1);
    }

    #[test]
    fn audit_passes_live_pattern() {
        let mut b = CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Refl),
            local_markers: refl_marker_set(),
            name: Some("refl_marker".into()),
            source_loc: None,
        });
        let cert = b.snapshot(h.step());
        assert!(dead_pattern_audit(&cert).is_empty());
    }

    #[test]
    fn audit_reports_sibling_matched_steps_for_dead_marker() {
        let mut b = CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        let step_id = h.step();
        // Live marker (matches Refl).
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Refl),
            local_markers: refl_marker_set(),
            name: Some("live".into()),
            source_loc: None,
        });
        // Dead marker (matches Theory only — cert has Refl).
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Theory),
            local_markers: empty_marker_set(),
            name: Some("dead".into()),
            source_loc: None,
        });
        let cert = b.snapshot(step_id);
        let diags = dead_pattern_audit(&cert);
        assert_eq!(diags.len(), 1);
        // The dead marker reports that step 0 was matched by a
        // sibling (the live Refl marker).
        assert_eq!(diags[0].marker_index, 1);
        assert_eq!(diags[0].steps_matched_by_siblings.len(), 1);
        assert_eq!(diags[0].steps_matched_by_siblings[0].id, step_id.0);
    }

    #[test]
    fn source_loc_propagates_through_diagnostic() {
        use adsmt_cert::SourceLoc;
        let mut b = CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Theory),
            local_markers: empty_marker_set(),
            name: Some("traceable".into()),
            source_loc: Some(SourceLoc::new(42, 10)),
        });
        let cert = b.snapshot(h.step());
        let diags = dead_pattern_audit(&cert);
        assert_eq!(diags.len(), 1);
        let loc = diags[0].source_loc.as_ref().expect("source_loc present");
        assert_eq!(loc.line, 42);
        assert_eq!(loc.column, 10);
    }

    #[test]
    fn diagnostics_to_json_produces_versioned_document() {
        let cert = build_cert_with_one_refl();
        let json = diagnostics_to_json(&[]).expect("serialise");
        // The document must always include the schema version,
        // generator label, and an empty diagnostics array even
        // when no violations exist.
        assert!(json.contains("\"schema_version\""));
        assert!(json.contains("\"generator\""));
        assert!(json.contains("\"diagnostics\""));
        // Sanity: cert is consumable end-to-end via audit_to_json.
        let _ = audit_to_json(&cert).expect("audit_to_json");
    }

    #[test]
    fn diagnostics_to_json_includes_dead_marker_details() {
        let mut b = CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Theory),
            local_markers: empty_marker_set(),
            name: Some("a_marker_name".into()),
            source_loc: Some(SourceLoc::new(7, 3)),
        });
        let cert = b.snapshot(h.step());
        let json = audit_to_json(&cert).expect("serialise");
        assert!(json.contains("a_marker_name"));
        assert!(json.contains("\"warning\""));
        assert!(json.contains("\"line\": 7"));
        assert!(json.contains("\"column\": 3"));
    }

    #[test]
    fn compact_json_is_one_line() {
        let json = diagnostics_to_json_compact(&[]).expect("serialise");
        assert!(!json.contains('\n'));
    }
}

// === The unsoundness / vacuity LINTER wire (lu-kb / VC-side) ===
//
// The advisory unsoundness/vacuity linter (a pure OBSERVER behind the soundness
// firewall — it reads already-trusted solver outputs and emits side-channel
// diagnostics, never changing a verdict) shares the same `Severity` /
// `SourceLocPayload` / `JSON_SCHEMA_VERSION` envelope as the dead-pattern audit,
// so a single VS Code / Theia extension (and the `adsmt-lsp` server) consumes
// both surfaces uniformly. This module is the SMT-LIB / ITP-side wire; the
// typed-ASP face (`adsmt-ir-asp`, a separate crate) mirrors the same field
// layout in its own serde shape.

/// A stable identifier for a lint rule — lets an IDE / CI filter findings by
/// rule without parsing the message. Serialised in `kebab-case` (e.g.
/// `"vacuous-context"`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum LintRule {
    /// The keystone: the in-scope assumptions `H` are unsatisfiable on their own
    /// (the solver decided `unsat` for `SAT(H)`), so the obligation passes
    /// **vacuously**. `Info`/soft by default — intentional vacuity (`requires
    /// false`, unreachable arms) is common; hard only under an explicit opt-in.
    VacuousContext,
    /// The solver returned `unknown` on `H`, so vacuity could not be checked
    /// (silence, not evidence). Off by default — a soft epistemic note only.
    ContextUnknown,
    /// A `forall` with no / an over-permissive `:pattern` (the solver / MBQI
    /// guesses instantiations). `Info` — many trigger-free axioms are intentional.
    MissingTrigger,
    /// An ASP **unsafe variable** (a head / `not` / comparison variable not bound
    /// by a positive body atom → grounding drops instances).
    AspUnsafeVariable,
    /// An ASP **negative cycle** (decided by the L3 stable-model gate, not the
    /// perfect model).
    AspNonStratified,
    /// An ASP program with **no answer set** (the vacuity dual on the ASP face).
    AspVacuity,
}

/// One advisory lint finding — the unsoundness/vacuity linter's payload, in a
/// `serde::Serialize` shape for IDE / CI consumption (the same envelope as
/// [`DeadPatternDiagnostic`], so one consumer reads both).
#[derive(Clone, Debug, Serialize)]
pub struct LintDiagnostic {
    pub rule: LintRule,
    pub severity: Severity,
    /// Human-readable message ready for direct display. Per the linter's
    /// attribution discipline, a vacuity finding is phrased "the solver found
    /// these in-scope assumptions unsatisfiable on their own", never "your
    /// context is contradictory".
    pub message: String,
    /// Source location for an editor squiggle (when the producer can supply one).
    pub source_loc: Option<SourceLocPayload>,
    /// The 0-based `(check-sat)` sequence number this finding attaches to, on the
    /// SMT-LIB streaming face (`None` for a parse/elaborate-time finding).
    pub check_sat_seq: Option<u32>,
}

impl LintDiagnostic {
    /// Build a finding at a given severity.
    pub fn new(rule: LintRule, severity: Severity, message: impl Into<String>) -> Self {
        LintDiagnostic { rule, severity, message: message.into(), source_loc: None, check_sat_seq: None }
    }
    /// Attach a source location (builder style).
    pub fn at(mut self, loc: SourceLocPayload) -> Self {
        self.source_loc = Some(loc);
        self
    }
    /// Attach a `(check-sat)` sequence number (builder style).
    pub fn for_check_sat(mut self, seq: u32) -> Self {
        self.check_sat_seq = Some(seq);
        self
    }
}

/// Top-level JSON document for lint findings — the same versioned envelope as
/// [`DiagnosticsDocument`], with a `lints` array instead of `diagnostics`.
#[derive(Clone, Debug, Serialize)]
pub struct LintDocument {
    pub schema_version: u32,
    pub generator: &'static str,
    pub lints: Vec<LintDiagnostic>,
}

impl LintDocument {
    fn wrap(lints: &[LintDiagnostic]) -> Self {
        LintDocument {
            schema_version: JSON_SCHEMA_VERSION,
            generator: concat!("adsmt-lints v", env!("CARGO_PKG_VERSION")),
            lints: lints.to_vec(),
        }
    }
}

/// Render lint findings as a versioned, pretty-printed JSON document (for IDE /
/// `(get-lints)` consumption).
pub fn lints_to_json(lints: &[LintDiagnostic]) -> Result<String, AuditError> {
    Ok(serde_json::to_string_pretty(&LintDocument::wrap(lints))?)
}

/// Compact one-line JSON, for log streams / `--lint-format=json` pipelines.
pub fn lints_to_json_compact(lints: &[LintDiagnostic]) -> Result<String, AuditError> {
    Ok(serde_json::to_string(&LintDocument::wrap(lints))?)
}

#[cfg(test)]
mod vc_lint_tests {
    use super::*;

    #[test]
    fn lint_document_is_versioned_and_kebab_ruled() {
        let lints = [
            LintDiagnostic::new(
                LintRule::VacuousContext,
                Severity::Info,
                "the solver found these in-scope assumptions unsatisfiable on their own",
            )
            .for_check_sat(3),
            LintDiagnostic::new(LintRule::MissingTrigger, Severity::Info, "forall with no :pattern")
                .at(SourceLocPayload { line: 12, column: 4 }),
        ];
        let json = lints_to_json(&lints).expect("serialise");
        assert!(json.contains("\"schema_version\""));
        assert!(json.contains("\"generator\""));
        assert!(json.contains("\"lints\""));
        assert!(json.contains("\"vacuous-context\""), "rule id is kebab-case");
        assert!(json.contains("\"missing-trigger\""));
        assert!(json.contains("\"info\""), "severity is lowercase");
        assert!(json.contains("\"check_sat_seq\": 3"));
        assert!(json.contains("\"line\": 12"));
    }

    #[test]
    fn empty_lints_still_a_valid_document() {
        let json = lints_to_json(&[]).expect("serialise");
        assert!(json.contains("\"schema_version\""));
        assert!(json.contains("\"lints\": []"));
    }

    #[test]
    fn compact_is_one_line() {
        let json = lints_to_json_compact(&[LintDiagnostic::new(
            LintRule::AspVacuity,
            Severity::Info,
            "no answer set",
        )])
        .expect("serialise");
        assert!(!json.contains('\n'));
        assert!(json.contains("\"asp-vacuity\""));
    }
}
