import TreeRewritingGame.DisplayTree
import ProofWidgets 

open Lean Meta Elab Server Tactic ProofWidgets 

structure TreeDisplay extends PanelWidgetProps where 
  tree : DisplayTree
deriving RpcEncodable

@[widget_module]
def OrdinaryTreeDisplay : Component TreeDisplay where
  javascript := include_str ".." / "build" / "js" / "interactiveTreeDisplay.js"

syntax (name := tree_display) "with_tree_display" tacticSeq : tactic

@[tactic tree_display]
def treeDisplay : Tactic
  | stx@`(tactic| with_tree_display $tacs) => do
    let tgt ← withTransparency .instances do 
      reduceAll (← getMainTarget)
    let t ← (tgt.toDisplayTree).run .root 
    savePanelWidgetInfo stx ``OrdinaryTreeDisplay do
      return json% { tree : $(← rpcEncode t) }
    evalTacticSeq tacs
  | _ => throwUnsupportedSyntax

example : True := by 
  with_panel_widgets[GoalTypePanel]
  sorry 

example (P Q : Prop) : P ∧ Q → Q ∧ P := by 
  with_tree_display
    sorry

example (P : Prop) : P = True → P := by 
  with_panel_widgets[GoalTypePanel]
  sorry

example (x : Nat) (P : (Nat → Nat) → Prop) : ∀y : Nat → Nat, P y := by 
  with_panel_widgets[GoalTypePanel]
  sorry


