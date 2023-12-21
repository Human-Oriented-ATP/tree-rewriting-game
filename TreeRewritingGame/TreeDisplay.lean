import TreeRewritingGame.DisplayTree
import ProofWidgets 

open Lean Meta Elab ProofWidgets 

structure TreeDisplayProps where 
  tree : DisplayTree

#mkrpcenc TreeDisplayProps

@[widget_module]
def TreeDisplay : Component TreeDisplayProps where
  javascript := include_str ".." / "build" / "js" / "treeDisplay.js"

open scoped Jsx in
def DisplayTree.draw (t : DisplayTree) : Html := <TreeDisplay tree={t}/>

@[expr_presenter]
def DisplayTree.presenter : ExprPresenter where
  userName := "Tree Display"
  present e := do
    let t ← e.toDisplayTree
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

example : (fun x => x) 0 = 0 := by 
  with_panel_widgets[GoalTypePanel]
  sorry
