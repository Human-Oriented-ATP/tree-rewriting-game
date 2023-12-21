import ProofWidgets 
import Std.Data.Array.Basic

open Lean Meta

inductive DisplayTree where 
  | node: (label : String) → (children: Array DisplayTree) → DisplayTree
deriving Repr

open DisplayTree

def DisplayTree.leaf (label : String) := node label #[]

#mkrpcenc DisplayTree

def unfoldArguments : Expr → Expr × Array Expr
  | Expr.app f x => let (function, arguments) := unfoldArguments f
                    (function, arguments ++ #[x]) 
  | e => (e, #[])

def ppConst : String → String 
  | "@Eq" => "="
  | "@Function.comp" => "∘"
  | l => l

open Expr in 
partial def Lean.Expr.toDisplayTree (e : Expr) : MetaM (Option DisplayTree) := do 
  match e with 
  | e@(const ..) => let label := (← ppExpr e).pretty
                    return leaf $ ppConst label
  | fvar fvarId => let userFacingName := (← getLCtx).get! fvarId |>.userName
                   return leaf userFacingName.toString
  | mvar mvarId => return leaf mvarId.name.toString 
  | lit x => match x with 
             | .natVal n => return leaf (toString n)
             | .strVal s => return leaf s 
  | sort _ => return none 
  | app f x => do
      let (function, arguments) := unfoldArguments (Expr.app f x)
      let argumentsAsTrees := (← arguments.mapM Expr.toDisplayTree).reduceOption 
      match function with 
      | .const c _ => 
        if (← isInstance c) then 
          return none
        else 
          let label := (← ppExpr function).pretty
          return node (ppConst label) argumentsAsTrees
      | fvar fvarId => let userFacingName := (← getLCtx).get! fvarId |>.userName
                       return node userFacingName.toString argumentsAsTrees  
      | _ => -- mainly for the lambda case
        let some functionAsTree ← function.toDisplayTree 
            | throwError "Function {function} cannot be converted to DisplayTree"
        return node "app" (#[functionAsTree] ++ argumentsAsTrees)  
  | e@(Expr.forallE ..) =>
      Meta.forallTelescopeReducing e (fun fvars body => do
      let isDependent := body.hasAnyFVar (fun f => fvars.contains (fvar f))
      let bodyAsTree ← body.toDisplayTree
      if isDependent then
        let fvarsAsTrees ← fvars.mapM Expr.toDisplayTree
        return node "∀" (fvarsAsTrees ++ #[bodyAsTree]).reduceOption
      else 
        let fvarTypes ← fvars.mapM inferType
        let fvarTypesAsTrees ← fvarTypes.mapM Expr.toDisplayTree
        return node "→" (fvarTypesAsTrees ++ #[bodyAsTree]).reduceOption  
      )
  | e@(Expr.lam ..) => 
      lambdaTelescope e (fun fvars body => do
      let bodyTree ← body.toDisplayTree
      let fvarsAsTrees ← fvars.mapM Expr.toDisplayTree
      return node ("λ") (fvarsAsTrees ++ #[bodyTree]).reduceOption
      )
  | Expr.bvar _ => panic! "Unbound bvar in expression"
  | Expr.mdata _ e => e.toDisplayTree
  | Expr.letE .. => panic! "Unreduced let in expression"
  | Expr.proj .. => return none
