import TreeRewritingGame.DisplayTree
import ProofWidgets

open Lean Meta Elab Tactic ProofWidgets

structure MaskedTreeDisplay' where 
  tree : DisplayTree

#mkrpcenc MaskedTreeDisplay'

@[widget_module]
def MaskedTreeDisplay : Component MaskedTreeDisplay' where
  javascript := include_str ".." / "build" / "js" / "treeDisplay.js"

open scoped Jsx in
def DisplayTree.drawMasked (t : DisplayTree) : Html := <MaskedTreeDisplay tree={t}/>

@[expr_presenter]
def MaskedDisplayTree.presenter : ExprPresenter where
  userName := "Constants masked"
  present e := withTransparency .instances do
    let reduced ← reduceAll e
    let t ← reduced.toDisplayTree
    match t with 
    | some t => return (← t.withAliases).drawMasked
    | none => throwError "Cannot draw tree for expression {e}"
