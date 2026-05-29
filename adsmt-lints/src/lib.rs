//! Offline-first lint plugins for adsmt and lu-kb usage.
//!
//! # Why this crate exists
//!
//! Per the "Classical axiom imports (on-demand)" policy
//! (`prover_emit_policy.md` § "Pattern markers (cross-cutting)"),
//! dead-pattern detection in user heuristics — a declared
//! `StepPattern` matching zero cert steps — should be **silent
//! during normal `cargo build`/`cargo test`** and only surface
//! when invoked via `cargo dylint`, where it lands as a
//! `Warn`-level lint named `adsmt_dead_heuristic_pattern`.
//!
//! This crate is the home for that lint plus any future
//! offline-first lints, including symmetrical lu-kb-side checks
//! (e.g. dead lu-kb predicate detection) that share the same
//! checker / type infrastructure. The shared location is
//! intentional — the v1.0 logicutils+adsmt unification (per
//! `logicutils_version_rule.md` rule 3) will inherit the lints
//! crate as-is.
//!
//! # v0.17 scaffold
//!
//! v0.17 ships:
//!
//! - The [`LINT_NAME`] / [`LINT_LEVEL`] constants — the official
//!   identifiers for `adsmt_dead_heuristic_pattern`.
//! - A pure-library [`analyse_dead_patterns`] entry point that
//!   takes a sequence of declared `StepPattern`s and a sequence
//!   of cert steps, and returns the patterns that matched zero
//!   steps. Library-form lets the same analysis run from tests
//!   without `cargo-dylint` infrastructure.
//! - Placeholder types so the crate compiles cleanly on stable
//!   Rust.
//!
//! v0.18 lifts the crate into a proper `cargo-dylint` plugin: a
//! `cdylib` crate exporting `register_lints` and wiring rustc's
//! lint pass to call [`analyse_dead_patterns`] over the parsed
//! cert. The library entry point above is the seam that v0.18
//! reuses unchanged.

use thiserror::Error;

/// The lint name exposed to `cargo dylint`.
///
/// `cargo dylint --lib adsmt-lints` will list this lint;
/// invocations that opt into it (via `#![warn(adsmt_dead_heuristic_pattern)]`
/// or registry-level config) produce diagnostics from
/// [`analyse_dead_patterns`].
pub const LINT_NAME: &str = "adsmt_dead_heuristic_pattern";

/// Default lint level. `Warn` per the v0.17 design decision —
/// dead patterns are hygiene concerns, not correctness failures.
pub const LINT_LEVEL: LintLevel = LintLevel::Warn;

/// Rustc-style lint level. We don't pull in `rustc_lint` directly
/// because v0.17 keeps this crate buildable on stable Rust; the
/// enum here mirrors rustc's `Level` shape so v0.18 can swap the
/// alias when the cdylib plugin lands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LintLevel {
    Allow,
    Warn,
    Deny,
    Forbid,
}

/// Lightweight stand-in for the eventual `StepPattern` shape that
/// lives in `adsmt-cert`. The lint analysis itself only needs to
/// know whether the pattern matched some step, so a stub identity
/// type is sufficient at the scaffold stage.
#[derive(Debug, Clone)]
pub struct DeclaredPattern {
    /// Caller-supplied identifier (typically the cert producer's
    /// pattern name) used to attribute the lint diagnostic.
    pub name: String,
    /// Caller-supplied match predicate: returns true when the
    /// pattern matches the i-th step (by step index in the cert).
    /// v0.18 replaces this with a richer reflection of
    /// `StepPattern`, but the analyse function signature stays
    /// the same.
    pub matches_step: fn(usize) -> bool,
}

/// Dead-pattern diagnostic — one per [`DeclaredPattern`] that
/// failed to match any cert step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadPatternDiagnostic {
    pub pattern_name: String,
    pub message: String,
}

#[derive(Debug, Error)]
pub enum LintError {
    #[error("internal lint error: {0}")]
    Internal(String),
}

/// Detect declared patterns that match zero steps.
///
/// Reusable from `cargo test` (today) or from a rustc lint pass
/// (v0.18). The output is one diagnostic per dead pattern; an
/// empty output means every declared pattern matched at least
/// one step.
pub fn analyse_dead_patterns(
    declared: &[DeclaredPattern],
    step_count: usize,
) -> Result<Vec<DeadPatternDiagnostic>, LintError> {
    let mut out = Vec::new();
    for pattern in declared {
        let mut matched = false;
        for step_idx in 0..step_count {
            if (pattern.matches_step)(step_idx) {
                matched = true;
                break;
            }
        }
        if !matched {
            out.push(DeadPatternDiagnostic {
                pattern_name: pattern.name.clone(),
                message: format!(
                    "{}: declared pattern `{}` matched 0 cert steps",
                    LINT_NAME, pattern.name,
                ),
            });
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn never_matches(_: usize) -> bool { false }
    fn matches_first(idx: usize) -> bool { idx == 0 }

    #[test]
    fn lint_name_and_level_are_canonical() {
        assert_eq!(LINT_NAME, "adsmt_dead_heuristic_pattern");
        assert_eq!(LINT_LEVEL, LintLevel::Warn);
    }

    #[test]
    fn empty_declared_set_produces_no_diagnostics() {
        let diags = analyse_dead_patterns(&[], 5).expect("no declared, no error");
        assert!(diags.is_empty());
    }

    #[test]
    fn pattern_matching_zero_steps_is_dead() {
        let declared = vec![DeclaredPattern {
            name: "always_false".into(),
            matches_step: never_matches,
        }];
        let diags = analyse_dead_patterns(&declared, 5).expect("analyse");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].pattern_name, "always_false");
        assert!(diags[0].message.contains(LINT_NAME));
    }

    #[test]
    fn pattern_matching_at_least_one_step_is_live() {
        let declared = vec![DeclaredPattern {
            name: "matches_first".into(),
            matches_step: matches_first,
        }];
        let diags = analyse_dead_patterns(&declared, 5).expect("analyse");
        assert!(diags.is_empty());
    }

    #[test]
    fn cert_with_zero_steps_marks_every_pattern_dead() {
        // Edge case — a cert with no steps means every declared
        // pattern is trivially dead. v0.17 still flags it; v0.18
        // may add a separate "empty cert" suppression rule.
        let declared = vec![
            DeclaredPattern {
                name: "p1".into(),
                matches_step: matches_first,
            },
            DeclaredPattern {
                name: "p2".into(),
                matches_step: never_matches,
            },
        ];
        let diags = analyse_dead_patterns(&declared, 0).expect("analyse");
        assert_eq!(diags.len(), 2);
    }
}

// === Future lu-kb-side lints ===
//
// Reserved space for lints targeting lu-kb usage patterns
// (e.g. unused predicate detection, kb-side dead rule
// detection). These share the [`DeclaredPattern`] / [`LintLevel`]
// scaffolding above and follow the same library-first /
// cargo-dylint-second deployment order.
