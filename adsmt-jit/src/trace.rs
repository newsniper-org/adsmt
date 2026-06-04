//! Trace representation — guards + skeleton-shape key.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use adsmt_core::{Term, TermInner};

use crate::guard::JitGuard;

/// 64-bit skeleton-shape hash.  Computed by [`SkeletonShape::of`]
/// over a `Term`'s `(and|or|=>|not)` shape down to depth-3 (as
/// per the §3.2 proposal text); equivalent skeletons under
/// `α`-renaming collide on the same hash, which is exactly the
/// equivalence the JIT cache wants to key on.
///
/// Two skeletons with the same hash *may* differ deeper than the
/// truncated depth — the `SkeletonShape` guard is necessary but
/// not sufficient.  The full liveness check goes through the
/// remaining [`JitGuard::PolyInvariant`] / [`JitGuard::EquivClass`]
/// records before the trace fires.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SkeletonShape(pub u64);

impl SkeletonShape {
    /// Compute the depth-3 truncated skeleton hash of `t`.
    /// `α`-renaming-stable: variable names dissolve into a single
    /// `"Var"` marker so two structurally-similar terms with
    /// different binder names produce the same hash.
    pub fn of(t: &Term) -> SkeletonShape {
        let mut h = DefaultHasher::new();
        Self::feed(t, 0, &mut h);
        SkeletonShape(h.finish())
    }

    fn feed(t: &Term, depth: u32, h: &mut DefaultHasher) {
        if depth >= 3 {
            "*".hash(h);
            return;
        }
        match t.kind() {
            TermInner::Var(_) => "Var".hash(h),
            TermInner::Const(c) => {
                "Const".hash(h);
                c.name.hash(h);
            }
            TermInner::App(f, x) => {
                "App".hash(h);
                Self::feed(f, depth + 1, h);
                Self::feed(x, depth + 1, h);
            }
            TermInner::Lam(_, body) => {
                "Lam".hash(h);
                Self::feed(body, depth + 1, h);
            }
        }
    }
}

/// Trace-cache key.  Currently just the skeleton hash; future
/// versions may extend with theory-bitmask or assertion-count
/// shards if cache contention becomes a real issue.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraceKey(pub SkeletonShape);

/// One recorded specialisation: a list of guards that must hold
/// for the trace to apply, plus an opaque kernel-id pointing to
/// the specialised propagation code.  The kernel-id is a `u32`
/// in v0 — the actual compiled-kernel store lives outside this
/// crate (lands in the §3.2 follow-up that wires dynasm-rs into
/// the engine).
#[derive(Clone, Debug)]
pub struct Trace {
    /// Cache key; computed once at record-time so cache lookups
    /// stay O(1).
    pub key: TraceKey,
    /// Guards in the order they were observed.  `check_guard`
    /// short-circuits on the first failure, so cheap guards
    /// should be ordered first.
    pub guards: Vec<JitGuard>,
    /// Opaque kernel handle.  The interpretation lives with the
    /// compiled-kernel store outside this crate.
    pub kernel_id: u32,
}

impl Trace {
    /// Construct a trace from its parts.  Pure data record; no
    /// validation up-front because the guard list is the
    /// validator the cache lookup will run.
    pub fn new(skeleton: SkeletonShape, guards: Vec<JitGuard>, kernel_id: u32) -> Self {
        Self {
            key: TraceKey(skeleton),
            guards,
            kernel_id,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    #[test]
    fn skeleton_shape_alpha_renaming_collapses() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let s1 = SkeletonShape::of(&p);
        let s2 = SkeletonShape::of(&q);
        // Both are Var-shaped at depth 0; the v0 hash strips
        // variable names so the two collide.  This is the
        // `α`-renaming-stability the proposal text calls out.
        assert_eq!(s1, s2);
    }

    #[test]
    fn skeleton_shape_distinguishes_var_from_const() {
        let p = Term::var("p", Type::bool_());
        let c = Term::const_("c", Type::bool_());
        let s1 = SkeletonShape::of(&p);
        let s2 = SkeletonShape::of(&c);
        // Const carries its name into the hash (no `α`-rename
        // applies to constants — they're the structural anchors).
        assert_ne!(s1, s2);
    }

    #[test]
    fn skeleton_shape_truncates_at_depth_three() {
        // Build a deeply-nested App and a shallower one that
        // agree at depth 3.  The depth-3 truncation should
        // collapse them on the v0 grammar.
        let p = Term::var("p", Type::bool_());
        let not_p = Term::mk_not(p.clone()).unwrap();
        let not_not_p = Term::mk_not(not_p.clone()).unwrap();
        let not_not_not_p = Term::mk_not(not_not_p.clone()).unwrap();
        // Depth-3 truncation: the innermost `not_p` slot becomes
        // `"*"` regardless of what's under it.  Adding a fourth
        // `not` simply replaces that `"*"` payload by yet another
        // `"*"`, so the hash collides with the four-deep version.
        let s_four = SkeletonShape::of(&not_not_not_p);
        let p2 = Term::var("p", Type::bool_());
        let not_p2 = Term::mk_not(p2.clone()).unwrap();
        let not_not_p2 = Term::mk_not(not_p2.clone()).unwrap();
        let four_then_var = Term::mk_not(
            Term::mk_not(not_not_p2.clone()).unwrap(),
        )
        .unwrap();
        let s_four_b = SkeletonShape::of(&four_then_var);
        assert_eq!(s_four, s_four_b);
    }
}
