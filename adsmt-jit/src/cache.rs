//! Trace cache — `SkeletonShape` ↦ list of traces.
//!
//! The lookup path is the JIT's hot inner loop: every per-query
//! `(check-sat)` consults the cache once per top-level
//! assertion, so the lookup itself needs to be cheap.  The v0
//! shape uses a flat `HashMap<TraceKey, Vec<Trace>>` — keyed by
//! the depth-3 skeleton hash so distinct top-level shapes
//! (`forall`, `=>`, `and`-of-equalities, …) shard into different
//! buckets up-front.

use std::collections::HashMap;

use crate::guard::{check_guard, ClassesView, GuardResult};
use crate::trace::{SkeletonShape, Trace, TraceKey};

/// Compiled-trace cache.  Insert order is preserved per-bucket
/// so an `intern`-style replay still iterates traces in the
/// order the recorder produced them.
#[derive(Default, Clone, Debug)]
pub struct JitCache {
    by_skeleton: HashMap<TraceKey, Vec<Trace>>,
}

impl JitCache {
    /// Empty cache.  No buckets allocated until the first insert.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert `trace` under its own `TraceKey`.  No deduplication
    /// at v0 — the runtime is free to record many traces that
    /// share a skeleton; the guard list differentiates them.
    pub fn insert(&mut self, trace: Trace) {
        self.by_skeleton
            .entry(trace.key)
            .or_default()
            .push(trace);
    }

    /// Total number of cached traces, summed across buckets.
    pub fn len(&self) -> usize {
        self.by_skeleton.values().map(Vec::len).sum()
    }

    /// `true` iff [`Self::len`] is zero.
    pub fn is_empty(&self) -> bool {
        self.by_skeleton.values().all(Vec::is_empty)
    }

    /// Cheap-path replay: find the first cached trace whose
    /// guards all pass against the current `(basis, classes,
    /// live_skeleton)` snapshot.  Returns its `kernel_id`.
    ///
    /// Why not return the `Trace` itself: the engine-side caller
    /// only needs the kernel handle (it routes through its own
    /// compiled-kernel store).  Returning the handle directly
    /// keeps this crate independent of the compile-cache layout.
    pub fn lookup(
        &self,
        live_skeleton: SkeletonShape,
        basis: &[adsmt_theory_finite_field::polynomial::Polynomial],
        classes: ClassesView<'_>,
    ) -> Option<u32> {
        let bucket = self.by_skeleton.get(&TraceKey(live_skeleton))?;
        for trace in bucket {
            let all_pass = trace
                .guards
                .iter()
                .all(|g| check_guard(g, basis, classes, live_skeleton) == GuardResult::Pass);
            if all_pass {
                return Some(trace.kernel_id);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::guard::JitGuard;

    #[test]
    fn empty_cache_lookup_misses() {
        let cache = JitCache::new();
        let k = SkeletonShape(0xdead);
        assert!(cache.lookup(k, &[], &[]).is_none());
        assert!(cache.is_empty());
    }

    #[test]
    fn cache_returns_first_trace_whose_guards_all_pass() {
        let mut cache = JitCache::new();
        let key = SkeletonShape(0xbeef);
        // Two traces under the same key.  The first has a
        // SkeletonShape guard that won't match the live shape;
        // the second is unconstrained.  Lookup should return the
        // second.
        let bad = Trace::new(
            key,
            vec![JitGuard::SkeletonShape(SkeletonShape(0xc0de))],
            10,
        );
        let good = Trace::new(key, vec![], 20);
        cache.insert(bad);
        cache.insert(good);
        let hit = cache.lookup(key, &[], &[]).unwrap();
        assert_eq!(hit, 20);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn distinct_skeleton_keys_shard_independently() {
        let mut cache = JitCache::new();
        let k1 = SkeletonShape(0x01);
        let k2 = SkeletonShape(0x02);
        cache.insert(Trace::new(k1, vec![], 100));
        cache.insert(Trace::new(k2, vec![], 200));
        assert_eq!(cache.lookup(k1, &[], &[]), Some(100));
        assert_eq!(cache.lookup(k2, &[], &[]), Some(200));
        assert_eq!(cache.lookup(SkeletonShape(0xff), &[], &[]), None);
    }
}
