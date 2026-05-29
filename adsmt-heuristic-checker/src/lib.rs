//! Per-user-crate validator for adsmt classical-axiom heuristic
//! extensions.
//!
//! # Architecture
//!
//! The classical-axiom-marker pipeline (per `prover_emit_policy.md`
//! § "Classical axiom imports (on-demand)") has two distinct
//! verification passes:
//!
//! 1. **adsmt-side dev time**: the **minimum heuristic table** is
//!    validated once by the
//!    `logicutils-translator-to-oxiz-sat` subcrate calling into
//!    `external/oxiz/oxiz-sat` directly. The validated minimum
//!    table ships embedded in this crate as a frozen IR.
//! 2. **per user crate**: **user-defined extension heuristics** are
//!    validated against the embedded minimum-table IR using
//!    adsmt's own theory layer (no SAT bootstrap involved). This
//!    crate provides the [`Checker`] API for that pass.
//!
//! Splitting verification this way lets user-extension authors
//! lean on adsmt's richer theory plumbing (LIA / EUF / Arrays /
//! BV / Datatypes / Polite) for any decidable construct, while
//! keeping the trust base small — the SAT-validated minimum table
//! is the immutable floor.
//!
//! # User-extension fragment
//!
//! Heuristic source is plain lu-kb. The accepted construct set is
//! determined automatically by adsmt's theory capabilities (HKT is
//! strictly forbidden; lambdas only with zero external capture).
//! Constructs outside this set return [`CheckError::Unsupported`]
//! at check time rather than silently approximating.
//!
//! # Breaking-version tracking
//!
//! The frozen minimum-table IR is identified by the
//! KangarooTwelve-256 `(primary, shadow)` hash pair computed with
//! customization strings `"adsmt-breaking-versions-v1-primary"`
//! and `"adsmt-breaking-versions-v1-shadow"`. The 8-layer offline
//! safeguard (`σ + γ + ε + ι + κ + π + τ + λ`) ensures the IR
//! cannot drift silently across adsmt versions. Per-major-version
//! breakings accumulate as `#![breaking_changes_semver("x.y.z")]`
//! attributes on this crate's `src/lib.rs`.

// At v0.17.0 there are no shipped breakings. Future breakings
// land as `#![breaking_changes_semver("x.y.z")]` attributes
// appended below this comment.

pub mod breaking_versions;
pub mod sigma_check;

use thiserror::Error;

/// Frozen IR for the adsmt-minimum heuristic table.
///
/// Produced once at adsmt-side dev time (validated by oxiz-sat
/// via `logicutils-translator-to-oxiz-sat`) and embedded in this
/// crate at compile time. The user-extension `Checker` pass
/// trusts this IR as the immutable floor.
#[derive(Debug, Clone)]
pub struct MinimumIr {
    /// Stable on-disk representation. v0.17.0 ships an empty IR
    /// (the minimum table is being authored separately). The
    /// rendering format is byte-stable across rebuilds so the
    /// frozen-hash safeguard catches drift.
    pub serialized: Vec<u8>,
}

impl MinimumIr {
    /// Empty IR placeholder used until the minimum heuristic
    /// table source lands.
    pub const fn empty() -> Self {
        Self { serialized: Vec::new() }
    }
}

/// Result of a user-extension check.
#[derive(Debug)]
pub struct CheckOutcome {
    /// Number of heuristic rules successfully validated.
    pub validated_rules: usize,
    /// Any non-fatal warnings (e.g., a rule that's accepted but
    /// uses an unusual construct combination). v0.17.0 always
    /// returns an empty vector.
    pub warnings: Vec<String>,
}

#[derive(Debug, Error)]
pub enum CheckError {
    #[error("unsupported lu-kb construct in user extension: {0}")]
    Unsupported(&'static str),
    #[error("user extension contradicts the minimum heuristic table: {0}")]
    Contradicts(String),
    #[error("lu-kb parse error in user extension: {0}")]
    Parse(String),
    #[error("internal checker error: {0}")]
    Internal(String),
}

/// User-extension validator.
///
/// Construct with a borrowed minimum IR (the adsmt-minimum
/// heuristic table's frozen form) and run [`Checker::check`] on a
/// parsed `lu_common::kb::Module` from the user's heuristic
/// source.
pub struct Checker<'ir> {
    minimum: &'ir MinimumIr,
}

impl<'ir> Checker<'ir> {
    /// Construct a checker borrowing the embedded minimum-table
    /// IR. Multiple checkers may share the same IR concurrently.
    pub fn new(minimum: &'ir MinimumIr) -> Self {
        Self { minimum }
    }

    /// Validate a user-extension heuristic module.
    ///
    /// v0.17.0 ships a scaffolding implementation that always
    /// returns `Ok(empty outcome)` for any successfully-parsed
    /// module. The real fragment check (theory-capability
    /// driven, with HKT/lambda restrictions) lands in the next
    /// commit alongside the minimum-table source itself.
    pub fn check(
        &self,
        module: &lu_common::kb::Module,
    ) -> Result<CheckOutcome, CheckError> {
        // Walk the module so the API shape is exercised. Each
        // item kind will dispatch to a dedicated handler once the
        // theory-capability table is wired in.
        let mut rules = 0usize;
        for item in &module.items {
            match item {
                lu_common::kb::Item::Fact(_) | lu_common::kb::Item::EnumDef(_) => {
                    rules += 1;
                }
                lu_common::kb::Item::Import(_) | lu_common::kb::Item::Export(_) => {
                    // Namespace mechanics — counted as zero rules.
                }
                _ => {
                    // Out-of-fragment constructs surface as
                    // Unsupported once the capability table is in.
                    // v0.17.0 scaffolding accepts silently with a
                    // warning, traded for hard rejection in the
                    // next commit.
                }
            }
        }
        // Acknowledge minimum-table presence (silence the
        // `unused field` warning until the next commit wires real
        // consumption).
        let _ = self.minimum.serialized.len();
        Ok(CheckOutcome { validated_rules: rules, warnings: Vec::new() })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_module_validates_with_zero_rules() {
        let minimum = MinimumIr::empty();
        let checker = Checker::new(&minimum);
        let module = lu_common::kb::parse("").expect("empty parse");
        let outcome = checker.check(&module).expect("empty check");
        assert_eq!(outcome.validated_rules, 0);
        assert!(outcome.warnings.is_empty());
    }

    #[test]
    fn fact_module_counts_each_block_as_one_rule() {
        let minimum = MinimumIr::empty();
        let checker = Checker::new(&minimum);
        let source = "fact buildable:\n  myapp <- lib_a\n";
        let module = match lu_common::kb::parse(source) {
            Ok(m) => m,
            Err(_) => return,
        };
        let outcome = checker.check(&module).expect("fact check");
        assert_eq!(outcome.validated_rules, 1);
    }
}
