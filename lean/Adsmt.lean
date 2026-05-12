import Adsmt.Ffi
import Adsmt.Solver
import Adsmt.Tactic

/-!
# adsmt: Lean4 bindings

Public entry-point. Imports the FFI declarations, the high-level
`Solver` wrapper, and the `smt` / `smt_abduce` tactics.

The C ABI is loaded from `libadsmt_ffi` — built with
`cargo build --release -p adsmt-ffi`. Ensure the shared library is on
the loader path (`LD_LIBRARY_PATH` on Linux, etc.) before importing
this module.
-/

namespace Adsmt

/-- adsmt version reported by the FFI. -/
def version : IO String := do
  let cstr ← Ffi.version
  return cstr

end Adsmt
