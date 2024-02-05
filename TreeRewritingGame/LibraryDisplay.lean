import Lean 
import ProofWidgets
import TreeRewritingGame.Rule 
import Init.Data.Array.Basic

open Lean Meta Elab Tactic ProofWidgets

structure LibraryEntry where
  name : String
  rule : Rule

#mkrpcenc LibraryEntry

structure Library where 
  entries : Array LibraryEntry

#mkrpcenc Library

structure LibraryDisplayProps where 
  library : Library

#mkrpcenc LibraryDisplayProps

@[widget_module]
def LibraryDisplay : Component LibraryDisplayProps where
  javascript := include_str ".." / "build" / "js" / "libraryDisplay.js"

open scoped Jsx in
def LibraryDisplay.draw (l : Library) : Html := 
  <LibraryDisplay library={l}/>

syntax (name := displayLibraryCommand) "#displayLibrary " : command

def testLibrary : Array Name := #[`Nat.add_comm, `Nat.add_assoc, `Nat.mul_add]

def enumerateRules (rules : Array Rule) : Array LibraryEntry := 
  rules.mapIdx (fun idx rule => ⟨s!"Rule {idx}", rule⟩)

unsafe def evalLibraryUnsafe (stx : Term) : TermElabM Name := do
  let nameT := mkConst ``Name
  Term.evalTerm Name nameT stx

@[implemented_by evalTreeRuleUnsafe]
opaque evalLibrary : Term → TermElabM Name

open Command Lean.Server in
@[command_elab displayLibraryCommand]
def elabDisplayLibraryCommand : CommandElab := fun
  | stx@`(#displayLibrary) =>
    runTermElabM fun _ => do
      let library := testLibrary
      let calculateRules := library.mapM treeOfEqualityRule
      let rules := (← calculateRules).reduceOption
      let html := LibraryDisplay.draw ⟨enumerateRules rules⟩    
      savePanelWidgetInfo stx ``HtmlDisplayPanel do
        return json% { html: $(← rpcEncode html) }
  | stx => throwError "Unexpected syntax {stx}."

#displayLibrary
