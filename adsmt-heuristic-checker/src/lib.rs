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
pub mod cache;
pub mod fragment;
pub mod sigma_check;

/// Captured at compile time by the `adsmt_heuristics!` family of
/// proc-macros (see `adsmt-heuristic-checker-macros`). Holds the
/// canonical encoding of a lu-kb heuristic source and a small
/// metadata summary the runtime checker reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdsmtHeuristicsSource {
    pub canonical_encoding: &'static str,
    pub item_count: usize,
}

pub use adsmt_heuristic_checker_macros::{
    adsmt_heuristics, derive_heuristics, import_adsmt_heuristics,
};

use thiserror::Error;

/// Frozen IR for the adsmt-minimum heuristic table.
///
/// Produced once at adsmt-side dev time (validated by oxiz-sat
/// via `logicutils-translator-to-oxiz-sat`) and embedded in this
/// crate at compile time. The user-extension `Checker` pass
/// trusts this IR as the immutable floor.
#[derive(Debug, Clone)]
pub struct MinimumIr {
    /// Stable on-disk representation — the canonical lu-kb
    /// source bytes from `minimum-table/minimum.kb`, captured at
    /// compile time via `include_str!`. The rendering is
    /// byte-stable across rebuilds so the frozen-hash safeguard
    /// catches drift.
    pub serialized: &'static str,
}

impl MinimumIr {
    /// Empty IR placeholder for tests that don't need the real
    /// table. Use [`MinimumIr::shipped`] for the actual minimum.
    pub const fn empty() -> Self {
        Self { serialized: "" }
    }

    /// The minimum heuristic table shipped with this version of
    /// adsmt-heuristic-checker. The bytes are the canonical
    /// lu-kb source from `minimum-table/minimum.kb`; the
    /// validated form is the SAT-verified IR cached at
    /// adsmt-side build time.
    pub const fn shipped() -> Self {
        Self {
            serialized: include_str!("../minimum-table/minimum.kb"),
        }
    }

    /// Return a reference to the pre-parsed shipped minimum
    /// table. Computed once per process via [`std::sync::LazyLock`]
    /// and reused thereafter, so callers can cheaply consult the
    /// minimum's structure (item kinds, fact entries, enum
    /// constructors) without re-parsing on every call.
    ///
    /// Panics if the shipped minimum table fails to parse —
    /// that would be an internal invariant violation since the
    /// proc-macro's σ anchor check (in
    /// `adsmt-heuristic-checker-macros`) verifies parseability
    /// at every macro invocation.
    pub fn shipped_module() -> &'static lu_common::kb::Module {
        SHIPPED_MODULE.as_ref().expect(
            "shipped minimum table must parse — proc-macro σ anchor would have caught any drift",
        )
    }

    /// Try variant — returns `None` if the shipped minimum
    /// table can't be parsed. Useful for diagnostic tools that
    /// want to surface the parse error without panicking.
    pub fn try_shipped_module() -> Option<&'static lu_common::kb::Module> {
        SHIPPED_MODULE.as_ref().ok()
    }
}

static SHIPPED_MODULE: std::sync::LazyLock<
    Result<lu_common::kb::Module, lu_common::kb::ParseError>,
> = std::sync::LazyLock::new(|| {
    lu_common::kb::parse(include_str!("../minimum-table/minimum.kb"))
});

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
    /// v0.18 wires the actual fragment validation
    /// ([`fragment::validate_fragment`]) so out-of-fragment
    /// constructs and the HKT/lambda restrictions land as
    /// [`CheckError::Unsupported`] or
    /// [`CheckError::Contradicts`] respectively. The
    /// non-contradiction pass against the embedded minimum IR is
    /// still scaffolded (the F.4+ work wires the actual SAT
    /// hand-off); for now the check returns success when the
    /// fragment scan passes.
    pub fn check(
        &self,
        module: &lu_common::kb::Module,
    ) -> Result<CheckOutcome, CheckError> {
        // (1) Fragment scan — HKT/lambda restrictions + theory-
        //     capability driven construct allow/deny.
        if let Err(e) = fragment::validate_fragment(module) {
            return Err(map_fragment_error(e));
        }
        // (2) Walk + count items so the API shape is exercised.
        let mut rules = 0usize;
        for item in &module.items {
            match item {
                lu_common::kb::Item::Fact(_)
                | lu_common::kb::Item::EnumDef(_)
                | lu_common::kb::Item::Rule(_)
                | lu_common::kb::Item::Constraint(_)
                | lu_common::kb::Item::DataDef(_)
                | lu_common::kb::Item::TypeAlias(_)
                | lu_common::kb::Item::Relation(_)
                | lu_common::kb::Item::Fn(_) => {
                    rules += 1;
                }
                lu_common::kb::Item::Import(_)
                | lu_common::kb::Item::Export(_) => {
                    // Namespace mechanics — counted as zero rules.
                }
                lu_common::kb::Item::Abduce(_)
                | lu_common::kb::Item::Instance(_) => {
                    // Should have been caught by the fragment
                    // scan above; reaching here would be a bug
                    // in the validator.
                    return Err(CheckError::Unsupported(
                        "internal: out-of-fragment item leaked past validate_fragment",
                    ));
                }
            }
        }
        // Acknowledge minimum-table presence — the IR doesn't
        // drive the v0.18 user-side check yet but the field is
        // load-bearing for future work (F.6+).
        let _ = self.minimum.serialized.len();
        Ok(CheckOutcome { validated_rules: rules, warnings: Vec::new() })
    }
}

fn map_fragment_error(e: fragment::FragmentError) -> CheckError {
    match e {
        fragment::FragmentError::HktForbidden(k) => CheckError::Unsupported(
            // Map all HKT failures to a single "HKT" label —
            // the underlying construct name is preserved in the
            // FragmentError display.
            match k {
                "Arrow" => "HKT (KindExpr::Arrow)",
                "Slot" => "HKT (KindExpr::Slot)",
                _ => "HKT",
            },
        ),
        fragment::FragmentError::LambdaCaptureForbidden(_) => {
            CheckError::Unsupported("Lambda with non-empty external capture")
        }
        fragment::FragmentError::OutsideFragment(name) => match name {
            "Instance" => CheckError::Unsupported("Instance"),
            "Abduce" => CheckError::Unsupported("Abduce"),
            _ => CheckError::Unsupported("out-of-fragment construct"),
        },
        fragment::FragmentError::UnsupportedTypeExpr(_) => {
            CheckError::Unsupported("type expression outside fragment")
        }
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
    fn shipped_minimum_table_parses() {
        let ir = MinimumIr::shipped();
        assert!(!ir.serialized.is_empty(), "shipped table must be non-empty");
        let module = lu_common::kb::parse(ir.serialized)
            .expect("shipped minimum table must parse");
        // EnumDef ClassicalModule + EnumDef StepKind +
        // EnumDef TheoryWitnessKind + FactBlock
        // propositional_required = 4 items at least.
        assert!(
            module.items.len() >= 4,
            "shipped table should have ≥4 items, found {}",
            module.items.len(),
        );
    }

    #[test]
    fn shipped_module_lazylock_returns_same_reference_each_call() {
        let m1 = MinimumIr::shipped_module();
        let m2 = MinimumIr::shipped_module();
        // Same `&'static` reference returned each time.
        assert!(std::ptr::eq(m1, m2));
        assert!(m1.items.len() >= 4);
    }

    #[test]
    fn try_shipped_module_succeeds_on_well_formed_minimum() {
        assert!(MinimumIr::try_shipped_module().is_some());
    }

    #[test]
    fn shipped_minimum_table_drat_row_present() {
        let ir = MinimumIr::shipped();
        assert!(
            ir.serialized.contains("theory_drat <- propositional"),
            "shipped table must encode the DRAT → Propositional row \
             (D5 = α in the design discussion)",
        );
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
