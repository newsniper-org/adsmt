/-!
# adsmt FFI declarations

Direct bindings to the C ABI exported by `adsmt-ffi`. The return-code
constants mirror those in `adsmt-ffi/src/lib.rs`. Tactic / `Solver`
wrappers in sibling modules adapt these to ergonomic Lean APIs.

The FFI functions are declared as pure to avoid the
world-token calling convention Lean uses for `IO`. Each call site
wraps the result with `IO.toEIO` semantics (just `return`). Memory
safety is the caller's responsibility — see `Solver.close`.
-/

namespace Adsmt.Ffi

/-- Opaque pointer to a Rust-side `Solver`.
    Marshalled as a USize so we don't have to implement Lean's
    `lean_external_object_class`. `0` is the null handle. Memory is
    owned by Rust and must be released via [`freeSolver`]. -/
abbrev SolverPtr : Type := USize

/-- Result codes returned by `check_sat`. -/
inductive SatCode where
  | sat
  | unsat
  | unknown
  | abductive
  | error (code : Int)
deriving Repr, DecidableEq

def SatCode.ofInt : Int → SatCode
  | 0 => .sat
  | 1 => .unsat
  | 2 => .unknown
  | 3 => .abductive
  | n => .error n

-- Pure declarations so Lean uses the ordinary C calling convention.
-- The `IO` wrappers below provide the user-facing surface.

@[extern "adsmt_solver_new"]
private opaque newSolverImpl : Unit → SolverPtr

@[extern "adsmt_solver_free"]
private opaque freeSolverImpl : SolverPtr → Int32

@[extern "adsmt_solver_push"]
private opaque pushImpl : SolverPtr → Int32

@[extern "adsmt_solver_pop"]
private opaque popImpl : SolverPtr → UInt32 → Int32

@[extern "adsmt_solver_reset"]
private opaque resetImpl : SolverPtr → Int32

@[extern "adsmt_solver_check_sat"]
private opaque checkSatImpl : SolverPtr → Int32

-- IO-wrapped surface

def newSolver : IO SolverPtr := return newSolverImpl ()
def freeSolver (s : SolverPtr) : IO Unit := do
  let _ := freeSolverImpl s
  return ()
def push (s : SolverPtr) : IO Int32 := return pushImpl s
def popN (s : SolverPtr) (n : UInt32) : IO Int32 := return popImpl s n
def reset (s : SolverPtr) : IO Int32 := return resetImpl s
def checkSatRaw (s : SolverPtr) : IO Int32 := return checkSatImpl s

/-- v0.1 placeholder for the version FFI; once `adsmt_version` is
    wired up through a string-marshalling helper this will read the
    actual C string. -/
def version : IO String :=
  return "adsmt v0.1 (FFI placeholder)"

end Adsmt.Ffi
