import Adsmt.Ffi

/-!
# Solver wrapper

High-level Lean interface around the FFI. Owns a `SolverPtr` and
exposes ergonomic methods that map onto `Adsmt.Ffi` primitives.
-/

namespace Adsmt

open Adsmt.Ffi

/-- A live solver instance, freed when this value goes out of scope
    via `freeSolver` in `IO`. v0.1 keeps the resource handling
    explicit; v0.3 will wrap in a `Solver.run` continuation. -/
structure Solver where
  ptr : SolverPtr

/-- Create a fresh solver. -/
def Solver.new : IO Solver := do
  let p ← newSolver
  return { ptr := p }

/-- Free the underlying handle. After calling this, the `Solver`
    value must not be used. -/
def Solver.close (s : Solver) : IO Unit :=
  freeSolver s.ptr

def Solver.push (s : Solver) : IO Unit := do
  let _ ← Adsmt.Ffi.push s.ptr
  pure ()

def Solver.pop (s : Solver) (n : UInt32 := 1) : IO Unit := do
  let _ ← Adsmt.Ffi.popN s.ptr n
  pure ()

def Solver.reset (s : Solver) : IO Unit := do
  let _ ← Adsmt.Ffi.reset s.ptr
  pure ()

/-- Check satisfiability. The returned `SatCode` enum distinguishes
    `sat` / `unsat` / `unknown` / `abductive` / `error code`. -/
def Solver.checkSat (s : Solver) : IO SatCode := do
  let code ← checkSatRaw s.ptr
  return SatCode.ofInt code.toInt

end Adsmt
