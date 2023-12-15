import TreeRewritingGame.DisplayTree
import ProofWidgets 

open Lean Meta Elab Tactic ProofWidgets 

structure TreeDisplay where 
  tree : DisplayTree

#mkrpcenc TreeDisplay

@[widget_module]
def OrdinaryTreeDisplay : Component TreeDisplay where
  javascript := include_str ".." / "build" / "js" / "treeDisplay.js"

open scoped Jsx in
def DisplayTree.draw (t : DisplayTree) : Html := <OrdinaryTreeDisplay tree={t}/>

@[expr_presenter]
def DisplayTree.presenter : ExprPresenter where
  userName := "Tree Display"
  present e := withTransparency .instances do
    let reduced ← reduceAll e
    let t ← reduced.toDisplayTree
    match t with 
    | some t => return t.draw
    | none => throwError "Cannot draw tree for expression {e}"


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


