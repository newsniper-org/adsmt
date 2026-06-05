//! §3.2 compiled-kernel store + dynasm-rs runtime emit.
//!
//! Each `CdclTrace` that fires past the §3.5.F guard gate
//! eventually maps to a specialised propagation kernel — a
//! small chunk of machine code that re-executes the trace's
//! recorded state transitions on the engine's live CDCL state
//! without going through the generic propagation loop.  The
//! v0 surface defined `Trace::kernel_id: u32` as an "opaque
//! handle into the engine-side store" but never built the
//! store; this module is the store + the dynasm-rs glue that
//! actually emits the code.
//!
//! ## v0.x scope
//!
//! - [`KernelStore`] — append-only store of registered
//!   kernels.  `kernel_id: u32` is the index.
//! - [`CompiledKernel`] — RAII wrapper around dynasm-rs's
//!   `ExecutableBuffer` + the entry-point function pointer.
//! - [`emit_noop_kernel`] — minimal `ret`-only kernel.  Used
//!   as the v0.x placeholder for traces that pass the guard
//!   gate but don't yet have a real specialised kernel
//!   compiled.  Calling it is a single CPU `ret` instruction
//!   (no work, no observable side effect).
//! - [`KernelError`] — typed error surface
//!   (`UnsupportedHostTriple`, `Assemble`).
//!
//! ## Host-triple gating
//!
//! dynasm-rs's x64 module emits AMD64 machine code; on a
//! non-x86_64 host the `cfg(target_arch = "x86_64")` gates
//! every emit path off, and `register_emitted` immediately
//! surfaces [`KernelError::UnsupportedHostTriple`].  The
//! store itself (registration, lookup, drop) stays available
//! on every triple so the JIT cache + dispatcher can compile
//! cleanly anywhere; only the actual execute path is gated.

use std::mem;

#[cfg(target_arch = "x86_64")]
use dynasm::dynasm;
#[cfg(target_arch = "x86_64")]
use dynasmrt::{DynasmApi, ExecutableBuffer};

/// Error surface for kernel emit / register operations.
#[derive(Debug)]
pub enum KernelError {
    /// Running on a host triple dynasm-rs cannot emit for.
    /// v0.x: only `target_arch = "x86_64"` is supported; all
    /// others map here at register time.
    UnsupportedHostTriple { found: &'static str },
    /// dynasm-rs's `Assembler::finalize` failed (e.g. the
    /// emitted code referenced a label that was never defined).
    Assemble { message: String },
}

impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KernelError::UnsupportedHostTriple { found } => write!(
                f,
                "compiled-kernel emit is not supported on `{found}`; only x86_64 is wired at v0.x"
            ),
            KernelError::Assemble { message } => {
                write!(f, "dynasm finalize: {message}")
            }
        }
    }
}

impl std::error::Error for KernelError {}

/// RAII wrapper around an emitted machine-code buffer.  Drops
/// the underlying mmap when this value goes out of scope.
///
/// `entry: unsafe extern "C" fn() -> i64` — the v0.x signature
/// returns a 64-bit integer; the noop kernel returns 0,
/// future kernels return verdict-shaped sentinels the
/// dispatcher interprets.
pub struct CompiledKernel {
    /// RAII handle for the mmap that backs `entry`.  Read
    /// only for the executable-buffer lifetime side effect —
    /// dropping the kernel drops this buffer, which in turn
    /// munmaps the page the function pointer dereferences.
    /// `#[allow(dead_code)]` because the field is never
    /// observed by Rust code, only by `entry`'s call site.
    #[cfg(target_arch = "x86_64")]
    #[allow(dead_code)]
    buf: ExecutableBuffer,
    entry: unsafe extern "C" fn() -> i64,
}

impl CompiledKernel {
    /// Invoke the kernel.  Unsafe because the kernel runs raw
    /// machine code with no Rust-side type-safety guarantees;
    /// the caller is responsible for ensuring the kernel was
    /// emitted with the expected calling convention.
    ///
    /// v0.x kernels (`emit_noop_kernel`) return 0 and have no
    /// side effects, so calling them is safe in practice; the
    /// `unsafe` marker reserves the right to evolve.
    ///
    /// # Safety
    ///
    /// The kernel must have been emitted with the v0.x
    /// `unsafe extern "C" fn() -> i64` signature.  Misuse is
    /// undefined behaviour.
    pub unsafe fn invoke(&self) -> i64 {
        unsafe { (self.entry)() }
    }
}

impl std::fmt::Debug for CompiledKernel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompiledKernel")
            .field("entry", &(self.entry as usize))
            .finish()
    }
}

/// Append-only store of compiled kernels.  `kernel_id: u32`
/// is the index into `kernels`; once registered, a kernel
/// stays addressable for the lifetime of the store.
#[derive(Default)]
pub struct KernelStore {
    kernels: Vec<CompiledKernel>,
}

impl std::fmt::Debug for KernelStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KernelStore")
            .field("kernels", &self.kernels.len())
            .finish()
    }
}

impl KernelStore {
    /// Empty store, no kernels yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of registered kernels.
    pub fn len(&self) -> usize {
        self.kernels.len()
    }

    /// `true` iff [`Self::len`] is zero.
    pub fn is_empty(&self) -> bool {
        self.kernels.is_empty()
    }

    /// Register `kernel`; returns the kernel id.
    pub fn register(&mut self, kernel: CompiledKernel) -> u32 {
        let id: u32 = self
            .kernels
            .len()
            .try_into()
            .expect("kernel-id space > u32 is implausible");
        self.kernels.push(kernel);
        id
    }

    /// Convenience: emit a noop kernel + register it.  Returns
    /// the kernel id.  Available only on x86_64; other host
    /// triples surface [`KernelError::UnsupportedHostTriple`].
    pub fn register_emitted_noop(&mut self) -> Result<u32, KernelError> {
        let kernel = emit_noop_kernel()?;
        Ok(self.register(kernel))
    }

    /// Read-only borrow of a registered kernel.
    pub fn get(&self, id: u32) -> Option<&CompiledKernel> {
        self.kernels.get(id as usize)
    }
}

/// Emit a minimal noop kernel — a single `ret` instruction
/// that returns 0.  Used as the v0.x placeholder for traces
/// that the guard gate passed but the dispatcher doesn't yet
/// have a specialised kernel for.
///
/// On x86_64: emits the AMD64 encoding via dynasm-rs.
/// On other host triples: surfaces
/// [`KernelError::UnsupportedHostTriple`].
#[cfg(target_arch = "x86_64")]
pub fn emit_noop_kernel() -> Result<CompiledKernel, KernelError> {
    let mut ops = dynasmrt::x64::Assembler::new().map_err(|e| {
        KernelError::Assemble {
            message: format!("Assembler::new: {e}"),
        }
    })?;
    let entry_offset = ops.offset();
    dynasm!(ops
        ; .arch x64
        ; xor rax, rax
        ; ret
    );
    let buf = ops
        .finalize()
        .map_err(|e| KernelError::Assemble {
            message: format!("finalize: {e:?}"),
        })?;
    let entry_ptr = buf.ptr(entry_offset);
    // SAFETY: `entry_offset` points to the start of the
    // emitted code we just wrote (`xor rax, rax; ret`).  The
    // C calling convention places no args / returns `i64` via
    // `rax`; transmuting the raw pointer to a function
    // pointer is the dynasm-rs-blessed pattern.
    let entry: unsafe extern "C" fn() -> i64 =
        unsafe { mem::transmute(entry_ptr) };
    Ok(CompiledKernel { buf, entry })
}

/// Non-x86_64 fallback — surfaces an error at register time.
/// The store itself stays usable; only the emit path is
/// gated.
#[cfg(not(target_arch = "x86_64"))]
pub fn emit_noop_kernel() -> Result<CompiledKernel, KernelError> {
    Err(KernelError::UnsupportedHostTriple {
        found: std::env::consts::ARCH,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_store_has_zero_kernels() {
        let s = KernelStore::new();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
        assert!(s.get(0).is_none());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn emit_noop_kernel_returns_zero_when_invoked() {
        let kernel = emit_noop_kernel().expect("x86_64 noop emit must succeed");
        let r = unsafe { kernel.invoke() };
        assert_eq!(r, 0);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn register_emitted_noop_assigns_sequential_ids() {
        let mut store = KernelStore::new();
        let id0 = store.register_emitted_noop().unwrap();
        let id1 = store.register_emitted_noop().unwrap();
        assert_eq!(id0, 0);
        assert_eq!(id1, 1);
        assert_eq!(store.len(), 2);
        let k0 = store.get(id0).expect("kernel 0 registered");
        let r = unsafe { k0.invoke() };
        assert_eq!(r, 0);
    }

    #[cfg(not(target_arch = "x86_64"))]
    #[test]
    fn emit_noop_kernel_surfaces_unsupported_host_triple() {
        match emit_noop_kernel() {
            Err(KernelError::UnsupportedHostTriple { .. }) => {}
            other => panic!("expected UnsupportedHostTriple, got {other:?}"),
        }
    }
}
