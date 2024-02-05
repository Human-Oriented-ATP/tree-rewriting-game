import TreeRewritingGame.DisplayTree
import ProofWidgets 

open Lean Meta Elab Server Tactic ProofWidgets Json Jsx

structure TreeDisplayProps where
  tree : DisplayTree
  divStyle : Json := json% {
        height: "40%",
        display: "inline-flex",
        width: "100%",
        border: "1px solid rgba(100, 100, 100, 0.2)",
        overflow: "hidden", 
        resize: "both",
        opacity: "0.9"
    }
deriving RpcEncodable

@[widget_module]
def TreeDisplay : Component TreeDisplayProps where
  javascript := include_str ".." / "build" / "js" / "interactiveTreeDisplay.js"

syntax (name := tree_display) "with_tree_display" tacticSeq : tactic

def displayRewriteRule (lhs : Expr) (rhs : Expr) : MetaM Html := do
  let .some lhsTree ← lhs.toDisplayTreeAtRoot | throwError m!"Failed to display {lhs} as tree."
  let .some rhsTree ← rhs.toDisplayTreeAtRoot | throwError m!"Failed to display {rhs} as tree."
  return (
    <div style={json% {width: "100%", overflow: "hidden", display: "inline-flex"}}>
      <TreeDisplay tree={lhsTree} divStyle={json% {width:"50%", display:"inline-block"}} />
      <span style={json% {alignItems: "center", fontSize: "50px"}}>→</span>
      <TreeDisplay tree={rhsTree} divStyle={json% {width:"50%", display:"inline-block"}} />
    </div>
  )

@[tactic tree_display]
def treeDisplay : Tactic
  | stx@`(tactic| with_tree_display $tacs) => do
    let tgt ← withTransparency .instances do 
      reduceAll (← getMainTarget)
    let t ← (tgt.toDisplayTree).run .root 
    savePanelWidgetInfo stx ``TreeDisplay do
      return json% { tree : $(← rpcEncode t) }
    evalTacticSeq tacs
  | _ => Elab.throwUnsupportedSyntax

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


