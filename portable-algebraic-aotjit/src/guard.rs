//! FF-free algebraic-invariant guards.
//!
//! The portable subset of the §3.2 guard set: equivalence-class
//! containment and depth-3 skeleton-shape match. Both verify a
//! recorded invariant against the live state in O(1)–O(#classes)
//! before a trace fires.
//!
//! The third in-tree variant — `PolyInvariant(GF2Poly)` — is *not*
//! here: it reduces a polynomial against the live GF(2) basis and so
//! couples to the finite-field crate. Per the 2026-06-13 profile the
//! GF(2) basis is the superseded 99.4% the 32-byte clause-set digest
//! replaced (rc.34.3), so the portable core carries only the FF-free
//! guards; the in-tree `adsmt-jit::JitGuard` keeps `PolyInvariant` as
//! an FF-coupled superset and **delegates its `EquivClass` /
//! `SkeletonShape` arms to [`check_guard`] here** (one
//! implementation, zero churn at the construction sites and in the
//! `.lutrace` wire format).

/// One pinned, finite-field-free invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Guard {
    /// Two atoms must sit in the same UF congruence class. The host
    /// threads its class table in via [`ClassesView`] so this crate
    /// stays UF-agnostic.
    EquivClass { a: String, b: String },
    /// The depth-3 skeleton-shape hash of the current top-level
    /// formula matches the one the trace was recorded under. Compared
    /// as a single `u64`; the host computes the hash (the constructor
    /// over its own term type stays host-side).
    SkeletonShape(u64),
}

/// Outcome of [`check_guard`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum GuardResult {
    /// The recorded invariant still holds; keep checking.
    Pass,
    /// The invariant broke; the trace cannot fire — fall back to the
    /// interpreter (same shape as a classical value-guard miss).
    Fail,
}

/// Read-only view of the host's UF equivalence-class state at
/// guard-check time: a flat `(atom_name, class_id)` table the host
/// builds once per query.
pub type ClassesView<'a> = &'a [(String, u32)];

/// Check a single FF-free guard. Pure function; the same
/// `(guard, classes, live_skeleton)` triple always returns the same
/// answer.
///
/// `live_skeleton` — depth-3 hash of the current top-level formula,
/// precomputed once and reused across every `SkeletonShape` guard.
pub fn check_guard(guard: &Guard, classes: ClassesView<'_>, live_skeleton: u64) -> GuardResult {
    match guard {
        Guard::EquivClass { a, b } => {
            let lookup = |name: &str| -> Option<u32> {
                classes.iter().find(|(n, _)| n == name).map(|(_, id)| *id)
            };
            match (lookup(a), lookup(b)) {
                (Some(ia), Some(ib)) if ia == ib => GuardResult::Pass,
                _ => GuardResult::Fail,
            }
        }
        Guard::SkeletonShape(recorded) => {
            if *recorded == live_skeleton {
                GuardResult::Pass
            } else {
                GuardResult::Fail
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equiv_class_passes_when_atoms_share_class() {
        let classes = vec![("a".to_string(), 1), ("b".to_string(), 1)];
        let g = Guard::EquivClass { a: "a".into(), b: "b".into() };
        assert_eq!(check_guard(&g, &classes, 0), GuardResult::Pass);
    }

    #[test]
    fn equiv_class_fails_on_different_or_absent() {
        let classes = vec![("a".to_string(), 1), ("b".to_string(), 2)];
        let g = Guard::EquivClass { a: "a".into(), b: "b".into() };
        assert_eq!(check_guard(&g, &classes, 0), GuardResult::Fail);
        let g2 = Guard::EquivClass { a: "a".into(), b: "z".into() };
        assert_eq!(check_guard(&g2, &classes, 0), GuardResult::Fail);
    }

    #[test]
    fn skeleton_shape_exact_match() {
        let g = Guard::SkeletonShape(0xdead_beef);
        assert_eq!(check_guard(&g, &[], 0xdead_beef), GuardResult::Pass);
        assert_eq!(check_guard(&g, &[], 0xcafe_f00d), GuardResult::Fail);
    }
}
