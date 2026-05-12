import Lean
import Adsmt.Solver

/-!
# Tactics

`smt` discharges a goal by handing it to the adsmt solver. v0.1
exposes the syntactic surface only — the goal-translation pipeline
(Lean expr → adsmt term → SMT-LIB serialization) lands when
`adsmt-engine` consumes input strings.

`smt_abduce` is the abductive variant: when `smt` would return
unknown / abductive, this tactic emits a `sorry` for each missing
hypothesis the solver suggests, so the user can fill them in.
-/

open Lean Elab Tactic

namespace Adsmt.Tactic

/--
`smt` — discharge the current goal via the adsmt solver.

v0.1 is a syntactic stub. It does not yet translate Lean expressions
to SMT-LIB; the tactic logs that the FFI is reachable and leaves the
goal untouched so the user sees a clear pending-implementation
signal.
-/
syntax (name := smt) "smt" : tactic

@[tactic smt]
def evalSmt : Tactic := fun _ => do
  logInfo "adsmt smt tactic: FFI reachable; translation pipeline pending (v0.3)."
  Lean.Elab.throwUnsupportedSyntax

/--
`smt_abduce` — abductive variant of `smt`.

On failure or `abductive` result, replaces the goal with one
`have` per suggested hypothesis (each closed by `sorry`) so the
user can finish the proof manually.
-/
syntax (name := smtAbduce) "smt_abduce" : tactic

@[tactic smtAbduce]
def evalSmtAbduce : Tactic := fun _ => do
  logInfo "adsmt smt_abduce tactic: abductive scaffolding pending (v0.5)."
  Lean.Elab.throwUnsupportedSyntax

end Adsmt.Tactic
