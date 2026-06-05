//! §3.2 JIT registry — the joint `(JitCache, KernelStore)` pair
//! that the engine-side dispatcher consults on every replay
//! attempt.
//!
//! v0 shipped the cache and the store as two independent
//! crates worth of machinery without a single owner; the
//! engine had to plumb the `(JitCache, KernelStore)` pair
//! through every replay-path site by hand and re-implement
//! the `lookup → emit → insert` orchestration.  [`JitRegistry`]
//! wraps both halves behind one type so the dispatcher gets
//! a single entry point:
//!
//! ```text
//! registry.register_trace(trace)?;          // emit + cache
//! let kernel = registry.lookup_kernel(...)? // gate + retrieve
//! unsafe { kernel.invoke() };               // run specialised
//! ```
//!
//! v0.x semantics:
//!
//! - `register_trace` emits a noop kernel via
//!   [`crate::kernel::emit_noop_kernel`] + sets
//!   `trace.kernel_id` to the new store id + inserts the
//!   trace into the cache.  The specialised propagation
//!   kernel emit (one kernel per trace) is the v1 follow-up
//!   that replaces the noop with a real assembler fragment.
//! - `lookup_kernel` runs the v0 [`JitCache::lookup`] gate +
//!   resolves the returned kernel id against the store.
//!   Returns `None` on guard miss *or* on store miss (the
//!   latter would surface only if `register_trace` was never
//!   called for the recorded trace).

use crate::cache::JitCache;
use crate::guard::ClassesView;
use crate::kernel::{CompiledKernel, KernelError, KernelStore};
use crate::trace::{SkeletonShape, Trace};

/// Owned `(JitCache, KernelStore)` pair.  See module docs.
#[derive(Default)]
pub struct JitRegistry {
    cache: JitCache,
    store: KernelStore,
}

impl std::fmt::Debug for JitRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("JitRegistry")
            .field("cache", &self.cache)
            .field("store", &self.store)
            .finish()
    }
}

impl JitRegistry {
    /// Empty registry — no cached traces, no compiled kernels.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of cached traces.
    pub fn cached_traces(&self) -> usize {
        self.cache.len()
    }

    /// Number of compiled kernels in the store.
    pub fn compiled_kernels(&self) -> usize {
        self.store.len()
    }

    /// Register `trace`: emit a kernel (v0.x = noop), set
    /// `trace.kernel_id` to the new store id, insert into
    /// the cache.  Returns the assigned kernel id so the
    /// caller can cross-reference if needed.
    ///
    /// Errors only when the host triple is unsupported by
    /// the kernel emitter (see
    /// [`KernelError::UnsupportedHostTriple`]).  v0.x ships
    /// the x86_64 path; other triples surface the error and
    /// the trace is *not* inserted into the cache (callers
    /// fall through to the interpreter loop).
    pub fn register_trace(&mut self, mut trace: Trace) -> Result<u32, KernelError> {
        let id = self.store.register_emitted_noop()?;
        trace.kernel_id = id;
        self.cache.insert(trace);
        Ok(id)
    }

    /// Dispatcher entry point — runs the cache's guard gate +
    /// resolves the returned kernel id against the store.
    /// Returns a borrowed kernel reference; the caller is
    /// responsible for `unsafe` invocation.
    pub fn lookup_kernel(
        &self,
        live_skeleton: SkeletonShape,
        basis: &[adsmt_theory_finite_field::polynomial::Polynomial],
        classes: ClassesView<'_>,
    ) -> Option<&CompiledKernel> {
        let id = self.cache.lookup(live_skeleton, basis, classes)?;
        self.store.get(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::guard::JitGuard;

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64"))]
    #[test]
    fn register_trace_emits_noop_and_inserts_into_cache() {
        let mut registry = JitRegistry::new();
        let trace = Trace::new(SkeletonShape(0xbeef), vec![], 0);
        let id = registry.register_trace(trace).expect("noop emit must succeed");
        assert_eq!(id, 0);
        assert_eq!(registry.cached_traces(), 1);
        assert_eq!(registry.compiled_kernels(), 1);
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64"))]
    #[test]
    fn lookup_kernel_returns_compiled_kernel_on_guard_pass() {
        let mut registry = JitRegistry::new();
        let key = SkeletonShape(0xc0de);
        let trace = Trace::new(key, vec![], 0);
        registry.register_trace(trace).unwrap();
        let kernel = registry
            .lookup_kernel(key, &[], &[])
            .expect("guard passes on empty guard set");
        // Invoking the noop kernel returns 0.
        let r = unsafe { kernel.invoke() };
        assert_eq!(r, 0);
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64"))]
    #[test]
    fn lookup_kernel_misses_on_guard_fail() {
        let mut registry = JitRegistry::new();
        let key = SkeletonShape(0xc0de);
        let trace = Trace::new(
            key,
            vec![JitGuard::SkeletonShape(SkeletonShape(0xfeed))],
            0,
        );
        registry.register_trace(trace).unwrap();
        // Live skeleton differs from the guard's pinned hash.
        let miss = registry.lookup_kernel(key, &[], &[]);
        assert!(miss.is_none());
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64"))]
    #[test]
    fn distinct_traces_get_distinct_kernel_ids() {
        let mut registry = JitRegistry::new();
        let id0 = registry
            .register_trace(Trace::new(SkeletonShape(0x01), vec![], 0))
            .unwrap();
        let id1 = registry
            .register_trace(Trace::new(SkeletonShape(0x02), vec![], 0))
            .unwrap();
        assert_eq!(id0, 0);
        assert_eq!(id1, 1);
        assert_eq!(registry.compiled_kernels(), 2);
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64")))]
    #[test]
    fn register_trace_errors_on_unsupported_host() {
        let mut registry = JitRegistry::new();
        let trace = Trace::new(SkeletonShape(0), vec![], 0);
        match registry.register_trace(trace) {
            Err(KernelError::UnsupportedHostTriple { .. }) => {}
            other => panic!(
                "expected UnsupportedHostTriple, got {other:?}"
            ),
        }
        // Cache stays empty since the emit failed.
        assert_eq!(registry.cached_traces(), 0);
    }
}
