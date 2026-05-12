import Lean
import Adsmt.Solver

/-!
# Tactics

`smt` discharges goals using adsmt's logic. v0.1 handles the
*Boolean polarity contradiction* fragment:

> If the local context contains both `h₁ : P` and `h₂ : ¬P`, close
> the goal by `absurd h₁ h₂`.

The full FFI pipeline (`adsmt-smoke` executable) verifies the
engine end-to-end at *runtime*. The tactic itself runs at Lean's
*elaboration* time, where the FFI shared library is not yet loaded
into the interpreter; v0.3 will route through native-compiled
modules so the engine becomes the load-bearing reasoner.

`smt_abduce` is the abductive variant; full scaffolding lands in
v0.5 once the abductive engine plugs into Lean's `sorry`-based hole
mechanism.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace Adsmt.Tactic

/-- Strip a single leading `Not` from a Prop expression. Returns
    `(stripped, polarity)` where `polarity = true` means the original
    expression was positive, `false` for negated. -/
private def stripNot (e : Expr) : (Expr × Bool) :=
  match e with
  | .app (.const ``Not _) p => (p, false)
  | _ => (e, true)

/-- Collected hypothesis info. -/
private structure HypInfo where
  fvar : FVarId
  body : Expr
  polarity : Bool
deriving Inhabited

/-- Walk the local context collecting Prop hypotheses. -/
private def collectHyps : TacticM (Array HypInfo) := do
  let lctx ← getLCtx
  let mut acc : Array HypInfo := #[]
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← inferType (mkFVar ldecl.fvarId)
    let isProp ← isProp ty
    if isProp then
      let (body, polarity) := stripNot ty
      acc := acc.push { fvar := ldecl.fvarId, body, polarity }
  return acc

/-- Find a pair `(positive, negative)` of hypotheses with defEq bodies. -/
private def findContradiction (hyps : Array HypInfo) :
    TacticM (Option (FVarId × FVarId)) := do
  for i in [:hyps.size] do
    let h1 := hyps[i]!
    if !h1.polarity then continue
    for j in [:hyps.size] do
      if i == j then continue
      let h2 := hyps[j]!
      if h2.polarity then continue
      if (← isDefEq h1.body h2.body) then
        return some (h1.fvar, h2.fvar)
  return none

/--
`smt` — discharge the current goal using adsmt's logic.

v0.1 fragment: detects `h₁ : P, h₂ : ¬P` in the local context and
closes the goal by `absurd h₁ h₂`. The full engine pipeline is
exercised by the `adsmt-smoke` runtime executable; tactic-time
FFI integration lands in v0.3.
-/
syntax (name := smt) "smt" : tactic

@[tactic smt]
def evalSmt : Tactic := fun _ => do
  let hyps ← collectHyps
  match (← findContradiction hyps) with
  | some (posF, negF) =>
      let goal ← getMainGoal
      let posExpr := mkFVar posF
      let negExpr := mkFVar negF
      -- For goal `False`: apply negExpr to posExpr.
      -- For arbitrary `Q`: use `absurd` (auto-elimination).
      let goalType ← goal.getType
      let falseProof := mkApp negExpr posExpr  -- of type `False`
      if goalType.isConstOf ``False then
        goal.assign falseProof
      else
        -- `False.elim : {C : Sort u} → False → C`
        let proof ← mkAppOptM ``False.elim #[some goalType, some falseProof]
        goal.assign proof
      replaceMainGoal []
  | none =>
      throwError "adsmt smt (v0.1): no direct (h₁ : P, h₂ : ¬P) pair found in context"

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
