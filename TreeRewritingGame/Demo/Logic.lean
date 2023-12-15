import TreeRewritingGame.OrdinaryDisplay
import TreeRewritingGame.MaskedDisplay

open Lean Meta Elab Tactic ProofWidgets 

example : True := by 
  with_panel_widgets[GoalTypePanel]
  sorry 

example (P Q : Prop) : P ∧ Q → Q ∧ P := by 
  with_panel_widgets[GoalTypePanel]
  sorry

example (P : Prop) : P = True → P := by 
  with_panel_widgets[GoalTypePanel]
  sorry

example (x : Nat) (P : (Nat → Nat) → Prop) : ∀y : Nat → Nat, P y := by 
  with_panel_widgets[GoalTypePanel]
  sorry
