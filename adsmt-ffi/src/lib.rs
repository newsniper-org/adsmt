//! C ABI for adsmt. Stable from v1.0; subject to change pre-v1.
//!
//! Surface mirrors the design in sec 34:
//! - Opaque pointer to `Solver`.
//! - String-based input (SMT-LIB compatible) routed through
//!   `adsmt-parser`.
//! - Return codes 0/1/2/3 follow the CLI exit-code contract
//!   (sat/unsat/unknown/abductive).
//!
//! Current surface covers solver lifecycle, push/pop, check, and
//! abduction-state mutation. A finer-grained term-builder API and
//! the JSON-RPC daemon variant are tracked as separate
//! pre-v1.0 milestones.

use std::ffi::{c_char, CStr, CString};
use std::ptr;

use adsmt_core::{Term, Type};
use adsmt_engine::{SatResult, Solver};

/// Opaque handle. Allocated by [`adsmt_solver_new`], freed by [`adsmt_solver_free`].
pub struct AdsmtSolver(Solver);

/// SAT result codes returned by [`adsmt_solver_check_sat`].
pub const ADSMT_SAT: i32 = 0;
pub const ADSMT_UNSAT: i32 = 1;
pub const ADSMT_UNKNOWN: i32 = 2;
pub const ADSMT_ABDUCTIVE: i32 = 3;

/// Error codes for command-style operations (negative).
pub const ADSMT_ERR_NULL: i32 = -1;
pub const ADSMT_ERR_INVALID: i32 = -2;

/// Pointer marshalled as `usize` for Lean compatibility.
/// `0` represents a null handle.
type SolverHandle = usize;

fn handle_from(b: Box<AdsmtSolver>) -> SolverHandle {
    Box::into_raw(b) as SolverHandle
}

fn handle_to<'a>(h: SolverHandle) -> Option<&'a mut AdsmtSolver> {
    if h == 0 {
        None
    } else {
        // Safety: the handle came from `Box::into_raw` and the caller
        // contract guarantees it has not been freed.
        Some(unsafe { &mut *(h as *mut AdsmtSolver) })
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn adsmt_solver_new() -> SolverHandle {
    handle_from(Box::new(AdsmtSolver(Solver::new())))
}

/// Returns `0` on success, `ADSMT_ERR_NULL` when given a null handle.
///
/// # Safety
/// `h` must have been returned by [`adsmt_solver_new`] and not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_solver_free(h: SolverHandle) -> i32 {
    if h == 0 {
        return ADSMT_ERR_NULL;
    }
    drop(unsafe { Box::from_raw(h as *mut AdsmtSolver) });
    0
}

/// # Safety
/// `h` must be a live handle from [`adsmt_solver_new`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_solver_push(h: SolverHandle) -> i32 {
    match handle_to(h) {
        Some(s) => { s.0.push(); 0 }
        None => ADSMT_ERR_NULL,
    }
}

/// # Safety
/// `h` must be a live handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_solver_pop(h: SolverHandle, levels: u32) -> i32 {
    match handle_to(h) {
        Some(s) => { s.0.pop(levels); 0 }
        None => ADSMT_ERR_NULL,
    }
}

/// # Safety
/// `h` must be a live handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_solver_reset(h: SolverHandle) -> i32 {
    match handle_to(h) {
        Some(s) => { s.0.reset(); 0 }
        None => ADSMT_ERR_NULL,
    }
}

/// Assert a Boolean atom by numeric id with explicit polarity.
///
/// `atom_id` identifies the atom (caller-managed); the FFI synthesizes
/// a Boolean term `Var("atom_<id>", Bool)` internally. `polarity` is
/// `1` for positive, `0` for negative. Returns `0` on success.
///
/// This is the minimal v0.1 surface for Lean tactics and CLI parsers
/// that don't yet build full Lean→adsmt term translation; v0.3 will
/// supersede this with structured term construction.
///
/// # Safety
/// `h` must be a live handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_solver_assert_atom(
    h: SolverHandle,
    atom_id: u64,
    polarity: i32,
) -> i32 {
    let s = match handle_to(h) {
        Some(s) => s,
        None => return ADSMT_ERR_NULL,
    };
    let name = format!("atom_{atom_id}");
    let t = Term::var(&name, Type::bool_());
    s.0.assert_with_polarity(t, polarity != 0);
    0
}

/// Check satisfiability of currently asserted constraints.
///
/// Returns one of `ADSMT_SAT`, `ADSMT_UNSAT`, `ADSMT_UNKNOWN`,
/// `ADSMT_ABDUCTIVE`, or `ADSMT_ERR_NULL` on null input.
///
/// # Safety
/// `h` must be a live handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_solver_check_sat(h: SolverHandle) -> i32 {
    let s = match handle_to(h) {
        Some(s) => s,
        None => return ADSMT_ERR_NULL,
    };
    match s.0.check_sat() {
        SatResult::Sat => ADSMT_SAT,
        SatResult::Unsat { .. } => ADSMT_UNSAT,
        SatResult::Unknown { .. } => ADSMT_UNKNOWN,
        SatResult::Abductive { .. } => ADSMT_ABDUCTIVE,
    }
}

/// Return a human-readable version string. The pointer is owned by
/// the caller and must be freed with [`adsmt_string_free`].
#[unsafe(no_mangle)]
pub extern "C" fn adsmt_version() -> *mut c_char {
    let v = env!("CARGO_PKG_VERSION");
    CString::new(v).unwrap().into_raw()
}

/// # Safety
/// `s` must be a pointer returned by an adsmt FFI function (e.g.
/// `adsmt_version`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn adsmt_string_free(s: *mut c_char) {
    if !s.is_null() {
        drop(unsafe { CString::from_raw(s) });
    }
}

/// Convenience helper for tests: not part of the stable ABI.
///
/// # Safety
/// `s` must point to a NUL-terminated UTF-8 string.
#[doc(hidden)]
pub unsafe fn cstr_to_string(s: *const c_char) -> Option<String> {
    if s.is_null() {
        return None;
    }
    Some(unsafe { CStr::from_ptr(s) }.to_string_lossy().into_owned())
}

#[unsafe(no_mangle)]
#[doc(hidden)]
pub extern "C" fn adsmt_solver_assertion_count(h: SolverHandle) -> i32 {
    match handle_to(h) {
        Some(s) => s.0.all_assertions().len() as i32,
        None => ADSMT_ERR_NULL,
    }
}

#[unsafe(no_mangle)]
#[doc(hidden)]
pub extern "C" fn adsmt_null_string() -> *mut c_char {
    ptr::null_mut()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lifecycle_new_check_free() {
        let h = adsmt_solver_new();
        assert_ne!(h, 0);
        let r = unsafe { adsmt_solver_check_sat(h) };
        assert_eq!(r, ADSMT_SAT);
        assert_eq!(unsafe { adsmt_solver_free(h) }, 0);
    }

    #[test]
    fn push_pop_via_ffi() {
        let h = adsmt_solver_new();
        unsafe { adsmt_solver_push(h) };
        unsafe { adsmt_solver_push(h) };
        unsafe { adsmt_solver_pop(h, 2) };
        let r = unsafe { adsmt_solver_check_sat(h) };
        assert_eq!(r, ADSMT_SAT);
        assert_eq!(unsafe { adsmt_solver_free(h) }, 0);
    }

    #[test]
    fn version_string_roundtrip() {
        let v = adsmt_version();
        assert!(!v.is_null());
        let s = unsafe { cstr_to_string(v) }.unwrap();
        assert_eq!(s, env!("CARGO_PKG_VERSION"));
        unsafe { adsmt_string_free(v) };
    }

    #[test]
    fn null_handle_returns_err() {
        let r = unsafe { adsmt_solver_check_sat(0) };
        assert_eq!(r, ADSMT_ERR_NULL);
    }

    #[test]
    fn assert_atom_polarity_contradiction_is_unsat() {
        let h = adsmt_solver_new();
        // assert atom 0 positively, then negatively → conflict.
        assert_eq!(unsafe { adsmt_solver_assert_atom(h, 0, 1) }, 0);
        assert_eq!(unsafe { adsmt_solver_assert_atom(h, 0, 0) }, 0);
        let r = unsafe { adsmt_solver_check_sat(h) };
        assert_eq!(r, ADSMT_UNSAT);
        unsafe { adsmt_solver_free(h) };
    }

    #[test]
    fn assert_atom_distinct_ids_stay_sat() {
        let h = adsmt_solver_new();
        unsafe { adsmt_solver_assert_atom(h, 0, 1) };
        unsafe { adsmt_solver_assert_atom(h, 1, 0) };
        let r = unsafe { adsmt_solver_check_sat(h) };
        assert_eq!(r, ADSMT_SAT);
        unsafe { adsmt_solver_free(h) };
    }
}
