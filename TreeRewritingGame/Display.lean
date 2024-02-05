import TreeRewritingGame.DisplayTree
import TreeRewritingGame.Meta
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
  range : Lsp.Range := default
deriving RpcEncodable

@[widget_module]
def TreeDisplay : Component TreeDisplayProps where
  javascript := include_str ".." / "build" / "js" / "interactiveTreeDisplay.js"

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

structure InteractionProps extends PanelWidgetProps where
  range : Lsp.Range
deriving RpcEncodable

@[server_rpc_method]
def allowedTreeRewrites (props : InteractionProps) : RequestM (RequestTask Html) := do
  let #[selectedLoc] := props.selectedLocations | return .pure <span>Select a single location</span>
  let some goal := props.goals.find? (·.mvarId == selectedLoc.mvarId) | return .pure <span>No goals found</span>
  let ⟨_, .target pos⟩ := selectedLoc | return .pure <span>Select a location in the target</span>
  let doc ← RequestM.readDoc 
  goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let target := md.type
      let rules := extractRewriteRules target
      let elems : Array Html ← rules.concatMapM fun (thmName, symm) ↦ do
        let html? ← ifApplicableRewrite? pos target thmName symm displayRewriteRule
        return if let some html := html? then 
            #[html, 
              .ofComponent MakeEditLink (.ofReplaceRange doc.meta props.range <| createRewriteTacticCall thmName symm pos) #[]] 
          else 
            #[]
      return .pure <| .element "div" #[] elems
 
@[widget_module]
def TreeRewritingGame : Component TreeDisplayProps where
  javascript := include_str ".." / "build" / "js" / "treeRewritingGame.js"

syntax (name := tree_game) "tree_game" : tactic

@[tactic tree_game]
def treeGame : Tactic
  | stx@`(tactic| tree_game) => do
    let some stxRange := (← getFileMap).rangeOfStx? stx | return ()
    let tgt ← withTransparency .instances do 
      reduceAll (← getMainTarget)
    let t ← tgt.toDisplayTreeAtRoot
    savePanelWidgetInfo stx ``TreeRewritingGame do
      return json% { 
        tree : $(← rpcEncode t),
        range : $(stxRange) }
  | _ => Elab.throwUnsupportedSyntax

example : True := by 
  with_panel_widgets[GoalTypePanel]
  sorry

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  add_rewrite_rules [ `And.symm ]
  tree_game

example (P : Prop) : P = True → P := by 
  with_panel_widgets[GoalTypePanel]
  sorry

example (x : Nat) (P : (Nat → Nat) → Prop) : ∀y : Nat → Nat, P y := by 
  with_panel_widgets[GoalTypePanel]
  sorry


