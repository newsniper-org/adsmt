import Adsmt

open Adsmt
open Adsmt.Ffi

/-- Smoke test that exercises the FFI end-to-end. Eprintln is used so
    output survives any segfault during development. -/
def main : IO UInt32 := do
  IO.eprintln "adsmt-smoke: starting"
  let s ← Solver.new
  IO.eprintln s!"  · created solver (handle={s.ptr})"

  let r1 ← s.checkSat
  IO.eprintln s!"  · check_sat on empty → {repr r1}"

  s.push
  s.push
  IO.eprintln "  · pushed two scopes"

  s.pop 2
  IO.eprintln "  · popped two scopes"

  let r2 ← s.checkSat
  IO.eprintln s!"  · check_sat after pop → {repr r2}"

  s.reset
  IO.eprintln "  · reset complete"

  s.close
  IO.eprintln "adsmt-smoke: done"
  return 0
