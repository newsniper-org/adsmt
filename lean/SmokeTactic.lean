import Adsmt

open Adsmt.Tactic

/-! Compile-time check that `smt` discharges direct contradictions. -/

example (P : Prop) (h₁ : P) (h₂ : ¬P) : False := by
  smt

example (P : Prop) (Q : Prop) (h₁ : P) (h₂ : ¬P) : Q := by
  smt

example (P : Prop) (h₁ : ¬P) (h₂ : P) : False := by
  smt

def main : IO Unit := do
  IO.println "adsmt tactic compile-check passed."
