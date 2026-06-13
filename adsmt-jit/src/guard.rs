//! Algebraic-invariant guard set.
//!
//! Each variant is one shape of "invariant the trace pinned" the
//! cache replay-check can verify in O(1)–O(basis-size) time
//! before firing the specialised propagation kernel.  Per the
//! §3.2 proposal text, the v0 set is intentionally narrow:
//! polynomial relations, equivalence-class containment, and
//! depth-3 skeleton-shape matches.  Adding more is a v1 design
//! call; widening the v0 set without engine-side evidence of
//! payoff would just inflate the guard list and waste replay
//! time.

use adsmt_theory_finite_field::polynomial::Polynomial as GF2Poly;
use adsmt_theory_finite_field::reduction::reduce;

use crate::trace::SkeletonShape;

/// One pinned invariant.
#[derive(Clone, Debug)]
pub enum JitGuard {
    /// The recorded polynomial `p` is in the current query's
    /// ideal `I` iff `reduce(p, basis_of(I)).is_zero()`.  Holds
    /// iff that reduction collapses to zero against the live
    /// basis.  Shares the kernel with §3.4's UNSAT-certification
    /// path.
    PolyInvariant(GF2Poly),
    /// Two atoms must sit in the same UF congruence class.  The
    /// guard fires off of the engine's UF state — v0 receives
    /// the class lookup through the `classes` slice passed to
    /// [`check_guard`] so this crate stays UF-agnostic; the
    /// engine-side caller threads in whichever representation it
    /// maintains.
    EquivClass { a: String, b: String },
    /// The depth-3 skeleton-shape hash of the current top-level
    /// formula matches the one the trace was recorded under.
    /// Compared as a single `u64`.
    SkeletonShape(SkeletonShape),
}

// `GuardResult` and `ClassesView` now live in the portable
// `portable-algebraic-aotjit` crate and are re-exported verbatim so
// the in-tree `adsmt_jit::guard::{GuardResult, ClassesView}` are the
// *same* types the portable `check_guard` returns/consumes — the
// EquivClass / SkeletonShape arms below delegate to it.
pub use portable_algebraic_aotjit::{ClassesView, GuardResult};

/// Check a single guard.  Pure function; the same
/// `(guard, basis, classes, skeleton)` quadruple always returns
/// the same answer.
///
/// `basis` — the live GF(2) basis the per-query CNF reduces to.
/// `classes` — see [`ClassesView`].
/// `live_skeleton` — depth-3 hash of the current top-level
/// formula; precomputed once and reused across every
/// `SkeletonShape` guard in the trace.
pub fn check_guard(
    guard: &JitGuard,
    basis: &[GF2Poly],
    classes: ClassesView<'_>,
    live_skeleton: SkeletonShape,
) -> GuardResult {
    match guard {
        JitGuard::PolyInvariant(p) => {
            // The FF-coupled arm stays in-tree: `reduce` shares the
            // kernel with §3.4 (the same function the theory-layer
            // UNSAT certification calls). Holds iff the reduction
            // collapses to zero against the live basis.
            if reduce(p, basis).is_zero() {
                GuardResult::Pass
            } else {
                GuardResult::Fail
            }
        }
        // The two FF-free arms delegate to the portable `check_guard`
        // — one implementation, shared with any future non-adsmt
        // consumer.
        JitGuard::EquivClass { a, b } => portable_algebraic_aotjit::check_guard(
            &portable_algebraic_aotjit::Guard::EquivClass {
                a: a.clone(),
                b: b.clone(),
            },
            classes,
            live_skeleton.0,
        ),
        JitGuard::SkeletonShape(recorded) => portable_algebraic_aotjit::check_guard(
            &portable_algebraic_aotjit::Guard::SkeletonShape(recorded.0),
            classes,
            live_skeleton.0,
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_theory_finite_field::monomial::{Monomial, MonomialOrder};

    fn mono(_n_vars: usize, exps: &[u8]) -> Monomial {
        Monomial::from_exponents(exps)
    }

    fn poly(n_vars: usize, monos: Vec<Monomial>) -> GF2Poly {
        GF2Poly::from_monomials(n_vars, MonomialOrder::Grevlex, monos)
    }

    #[test]
    fn poly_invariant_passes_when_reduction_is_zero() {
        // 1 variable, basis = {x}.  Polynomial = x.  reduce(x, [x]) = 0 → Pass.
        let x = mono(1, &[1]);
        let p_x = poly(1, vec![x.clone()]);
        let basis = vec![p_x.clone()];
        let guard = JitGuard::PolyInvariant(p_x);
        let r = check_guard(&guard, &basis, &[], SkeletonShape(0));
        assert_eq!(r, GuardResult::Pass);
    }

    #[test]
    fn poly_invariant_fails_when_reduction_is_nonzero() {
        // 2 variables, basis = {x}.  Polynomial = y.  reduce(y, [x]) = y ≠ 0 → Fail.
        let x = mono(2, &[1, 0]);
        let y = mono(2, &[0, 1]);
        let p_x = poly(2, vec![x]);
        let p_y = poly(2, vec![y]);
        let basis = vec![p_x];
        let guard = JitGuard::PolyInvariant(p_y);
        let r = check_guard(&guard, &basis, &[], SkeletonShape(0));
        assert_eq!(r, GuardResult::Fail);
    }

    #[test]
    fn equiv_class_passes_when_atoms_share_class() {
        let classes = vec![("a".to_string(), 1), ("b".to_string(), 1)];
        let g = JitGuard::EquivClass {
            a: "a".to_string(),
            b: "b".to_string(),
        };
        let r = check_guard(&g, &[], &classes, SkeletonShape(0));
        assert_eq!(r, GuardResult::Pass);
    }

    #[test]
    fn equiv_class_fails_on_different_classes() {
        let classes = vec![("a".to_string(), 1), ("b".to_string(), 2)];
        let g = JitGuard::EquivClass {
            a: "a".to_string(),
            b: "b".to_string(),
        };
        let r = check_guard(&g, &[], &classes, SkeletonShape(0));
        assert_eq!(r, GuardResult::Fail);
    }

    #[test]
    fn equiv_class_fails_when_atom_absent() {
        let classes = vec![("a".to_string(), 1)];
        let g = JitGuard::EquivClass {
            a: "a".to_string(),
            b: "b".to_string(),
        };
        let r = check_guard(&g, &[], &classes, SkeletonShape(0));
        assert_eq!(r, GuardResult::Fail);
    }

    #[test]
    fn skeleton_shape_passes_on_exact_match() {
        let g = JitGuard::SkeletonShape(SkeletonShape(0xdead_beef));
        let r = check_guard(&g, &[], &[], SkeletonShape(0xdead_beef));
        assert_eq!(r, GuardResult::Pass);
    }

    #[test]
    fn skeleton_shape_fails_on_hash_mismatch() {
        let g = JitGuard::SkeletonShape(SkeletonShape(0xdead_beef));
        let r = check_guard(&g, &[], &[], SkeletonShape(0xcafe_f00d));
        assert_eq!(r, GuardResult::Fail);
    }
}
