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
