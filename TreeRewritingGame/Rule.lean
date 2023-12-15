import TreeRewritingGame.OrdinaryDisplay
import TreeRewritingGame.MaskedDisplay

open Lean Meta Elab Tactic ProofWidgets

def getLhsAndRhs (e : Expr) : MetaM $ Option (Expr × Expr) := 
  forallTelescopeReducing e (fun _ body => 
    let (function, arguments) := unfoldArguments body
    match function with 
    | .const `Eq _ => do 
        pure ((← reduceAll arguments[1]!), (← reduceAll arguments[2]!))
    | _ => pure none
  )

structure Rule where 
  lhs : DisplayTree
  rhs : DisplayTree
deriving Repr

def treeOfEqualityRule (rule : Name) : MetaM $ Option Rule := do
  let some constantInfo := (← getEnv).find? rule | pure none
  let type := constantInfo.type
  let some (lhs, rhs) ← getLhsAndRhs type | pure none
  let some lhsTree ← lhs.toDisplayTree | pure none
  let some rhsTree ← rhs.toDisplayTree | pure none
  return some ⟨lhsTree, rhsTree⟩  

#mkrpcenc Rule

structure RuleComponent where 
  rule : Rule

#mkrpcenc RuleComponent

@[widget_module]
def RuleDisplay : Component RuleComponent where
  javascript := include_str ".." / "build" / "js" / "treeRuleDisplay.js"

open scoped Jsx in
def Rule.draw (r : Rule) : Html := <RuleDisplay rule={r}/>

unsafe def evalTreeRuleUnsafe (stx : Term) : TermElabM Name := do
  let nameT := mkConst ``Name
  Term.evalTerm Name nameT stx

@[implemented_by evalTreeRuleUnsafe]
opaque evalTreeRule : Term → TermElabM Name

syntax (name := treeRuleCommand) "#treeRule " term : command

def Rule.masked (r : Rule) : CoreM Rule := do 
  return ⟨← r.lhs.withAliases, ← r.rhs.withAliases⟩ 

open Command Lean.Server in
@[command_elab treeRuleCommand]
def elabTreeRuleCommand : CommandElab := fun
  | stx@`(#treeRule $t:term) =>
    runTermElabM fun _ => do
      let rule ← evalTreeRule t
      let some rule  ← treeOfEqualityRule rule | return ()
      dbg_trace "{repr rule}"
      let ht := (← rule.masked).draw
      savePanelWidgetInfo stx ``HtmlDisplayPanel do
        return json% { html: $(← rpcEncode ht) }
  | stx => throwError "Unexpected syntax {stx}."


#treeRule `Nat.add_mul
