import TreeRewritingGame.TreeDisplay
import Std.Data.Option.Basic

open Lean Meta Elab Tactic ProofWidgets

def withLhsAndRhs (e : Expr) (f : (Expr × Expr) → MetaM α) : MetaM (Option α) := do
  forallTelescopeReducing e (fun _ body =>
    let (function, arguments) := unfoldArguments body
    match function with 
    | .const `Eq _ => do 
        return (← f ((← reduceAll arguments[1]!), (← reduceAll arguments[2]!)))
    | _ => return none
  )

structure Rule where 
  lhs : DisplayTree
  rhs : DisplayTree
deriving Repr

def treeOfEqualityRule (rule : Name) : MetaM $ Option Rule := do
  let some constantInfo := (← getEnv).find? rule | pure none
  let type := constantInfo.type
  let result ← withLhsAndRhs type (fun (lhs, rhs)=> do 
    let some lhsTree ← lhs.toDisplayTree | pure none
    let some rhsTree ← rhs.toDisplayTree | pure none
    return some ⟨lhsTree, rhsTree⟩     
  )
  return Option.join result

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

open Command Lean.Server in
@[command_elab treeRuleCommand]
def elabTreeRuleCommand : CommandElab := fun
  | stx@`(#treeRule $t:term) =>
    runTermElabM fun _ => do
      let rule ← evalTreeRule t
      let some rule  ← treeOfEqualityRule rule | return ()
      let ht := rule.draw
      savePanelWidgetInfo stx ``HtmlDisplayPanel do
        return json% { html: $(← rpcEncode ht) }
  | stx => throwError "Unexpected syntax {stx}."

#treeRule `Nat.add_mul
