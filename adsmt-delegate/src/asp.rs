//! ASP **weak-constraint** delegation (L5 first slice) — wraps
//! `adsmt-ir-asp`'s [`solve_weak_optimal`] for external callers, mirroring
//! [`crate::oxiz::proves_goal`]'s SHAPE: one clear boundary function taking an
//! already-checkable input and returning a TRUSTED result.
//!
//! ## Why there is no MaxSAT *search* here
//!
//! Section 4 of this slice's design asked for a module that "constructs
//! `oxiz_sat`/`oxiz_opt` values directly via the Rust API: build the hard CNF
//! … add the `SoftClause`s … run the MaxSAT search, decode the result". This
//! module deliberately does **not** do that literally, and the deviation is
//! worth stating plainly for review:
//!
//! `adsmt_ir_asp::solve::solve_weak_optimal` already closes the trust
//! boundary by construction — it reuses the SAME GL-reduct-VERIFIED candidate
//! answer-set enumeration [`adsmt_ir_asp::solve`] runs for an ordinary
//! `solve()` call, and picks the cost-minimal candidate(s) by a plain
//! evaluation (see that function's doc comment for the full argument: the
//! finite candidate set is already fully, soundly enumerated, so optimizing
//! over it is an argmin, not a new search procedure). By the time a
//! candidate model reaches this crate, its atoms are already fully decided —
//! there is nothing left for a SAT/MaxSAT solver to search for, only a cost
//! to report. Wrapping that already-decided cost in a fresh `oxiz_sat::Solver`
//! call would add a new (untrusted-until-proven) search surface for zero
//! soundness or performance benefit — exactly the "ambitious combined
//! search" this slice's own design notes say to prefer against when a
//! simpler, provably-correct path exists.
//!
//! What this module DOES take from `oxiz-opt`, honoring the spirit of the
//! ask: the returned cost is rendered as `oxiz-opt`'s own
//! [`oxiz_opt::maxsat::Weight`] type (`Weight::Int`, arbitrary-precision —
//! not `i64`-overflow-prone) rather than a bare integer, for arithmetic-type
//! parity with the rest of the delegation stack and so a caller composing
//! this cost into a LARGER external `oxiz-opt` optimization later has the
//! right currency to add it in. Constructing the full `SoftClause`/`Lit`
//! CNF encoding (for such a composition) is deferred — no current caller
//! needs it, and it would require exposing new atom-to-`Lit` numbering
//! machinery with no consumer yet; see the P2 report for this explicit scope
//! call.
//!
//! ## Trust
//!
//! Every [`FaceError`] `adsmt-ir-asp` can raise (parse, elaboration,
//! unsafe-rule, multi-level, or a stable-model-enumeration budget overrun)
//! propagates unchanged — never silently narrowed to a partial/possibly-wrong
//! optimum.

use adsmt_ir_asp::ast::Atom;
use adsmt_ir_asp::{FaceError, elaborate, parse, solve_weak_optimal};
use num_bigint::BigInt;
use oxiz_opt::maxsat::Weight;

/// The trusted result of optimizing a typed-ASP program's weak constraints
/// (L5 first slice, single optimization level).
#[derive(Debug, Clone)]
pub struct AspWeakResult {
    /// Whether the program has an answer set at all (same meaning as
    /// `adsmt_ir_asp::solve::Solution::consistent`) — `false` iff no
    /// (hard-)constraint-consistent answer set exists, in which case `cost`
    /// is `None` and `models` is empty.
    pub consistent: bool,
    /// The minimal weak-constraint cost among the program's constraint-
    /// consistent answer set(s), as `oxiz-opt`'s own [`Weight`] type
    /// (always `Weight::Int`, this slice being integer-weight-only).
    /// `None` iff `!consistent`.
    pub cost: Option<Weight>,
    /// EVERY cost-minimal answer set (surface form, sorted); more than one
    /// iff several answer sets tie for the minimal cost.
    pub models: Vec<Vec<Atom>>,
}

/// Parse + elaborate + solve a typed-ASP source's weak constraints — the one
/// boundary function this module exposes. Propagates the SAME [`FaceError`]
/// `adsmt-ir-asp` would raise for a malformed / unsafe / multi-level /
/// over-budget program (see the module doc's "Trust" section).
pub fn solve_weak_optimal_src(src: &str) -> Result<AspWeakResult, FaceError> {
    let program = parse(src)?;
    let elab = elaborate(&program)?;
    solve_weak_optimal_program(&elab)
}

/// The same boundary as [`solve_weak_optimal_src`], for a caller that has
/// already parsed + elaborated the program (e.g. to also inspect ordinary
/// query answers via `adsmt_ir_asp::solve::solve` on the same [`Elaborated`]).
pub fn solve_weak_optimal_program(
    elab: &adsmt_ir_asp::Elaborated,
) -> Result<AspWeakResult, FaceError> {
    let w = solve_weak_optimal(elab)?;
    Ok(AspWeakResult {
        consistent: w.consistent,
        cost: w.cost.map(|c| Weight::Int(BigInt::from(c))),
        models: w.models,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wraps_the_trusted_cost_as_an_oxiz_weight() {
        let r = solve_weak_optimal_src("pred a. a. :~ a. [7@0]").unwrap();
        assert!(r.consistent);
        assert_eq!(r.cost, Some(Weight::Int(BigInt::from(7))));
        assert_eq!(r.models.len(), 1);
    }

    #[test]
    fn no_answer_set_is_none_cost() {
        let r = solve_weak_optimal_src("pred p. p :- not p. :~ p. [1@0]").unwrap();
        assert!(!r.consistent);
        assert_eq!(r.cost, None);
        assert!(r.models.is_empty());
    }

    #[test]
    fn propagates_the_single_level_rejection() {
        let err =
            solve_weak_optimal_src("pred a. pred b. a. b. :~ a. [1@0] :~ b. [1@1]").unwrap_err();
        assert!(matches!(err, FaceError::Unsupported(_)));
    }

    #[test]
    fn propagates_a_parse_error() {
        assert!(matches!(solve_weak_optimal_src(":~ a."), Err(FaceError::Parse(_))));
    }

    #[test]
    fn dedup_counting_survives_the_wrapper() {
        // same clingo-verified case as adsmt-ir-asp's own test: cost 5, not 15.
        let r =
            solve_weak_optimal_src("pred p(Int). p(1). p(2). p(3). :~ p(X). [5@0]").unwrap();
        assert_eq!(r.cost, Some(Weight::Int(BigInt::from(5))));
    }

    #[test]
    fn propagates_a_weight_overflow_error_rather_than_a_wrapped_cost() {
        // Regression for the confirmed P0 (adsmt-ir-asp/src/solve.rs's
        // `weak_cost`): before the fix, the i64 sum silently wrapped upstream
        // and this wrapper would have laundered the wrong value into a
        // `Weight::Int` that LOOKED trustworthy (arbitrary precision) despite
        // being built from an already-corrupted i64. The `?` in
        // `solve_weak_optimal_program` must surface the upstream abstain
        // as-is, not reach the `BigInt::from(c)` conversion at all.
        let err = solve_weak_optimal_src(
            "pred a. pred b. pred c.\n\
             a. b. c.\n\
             :~ a. [4611686018427387903@0]\n\
             :~ b. [4611686018427387904@0]\n\
             :~ c. [4611686018427387905@0]",
        )
        .unwrap_err();
        assert!(matches!(err, FaceError::Unsupported(_)));
    }
}
