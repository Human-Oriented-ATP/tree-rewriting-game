import ProofWidgets 
import Std.Data.Array.Basic
import TreeRewritingGame.DisplayAliasExtension

open Lean Meta

inductive DisplayTree where 
  | node: (label : String) → (children: Array DisplayTree) → DisplayTree
deriving Repr

open DisplayTree

def DisplayTree.leaf (label : String) := node label #[]

#mkrpcenc DisplayTree

partial def DisplayTree.withAliases : DisplayTree → CoreM DisplayTree 
  | node label children => do 
    let alias_ := match (← DisplayAlias.getAlias? label) with 
      | some alias_ => alias_
      | none => label 
    pure (node alias_ (← children.mapM DisplayTree.withAliases)) 

def unfoldArguments : Expr → Expr × Array Expr
  | Expr.app f x => let (function, arguments) := unfoldArguments f
                    (function, arguments ++ #[x]) 
  | e => (e, #[])

open Expr in 
partial def Lean.Expr.toDisplayTree (e : Expr) : MetaM (Option DisplayTree) := do 
  match e with 
  | e@(const ..) => let label := (← ppExpr e).pretty
                    DisplayAlias.addLabel label
                    return leaf label
  | fvar fvarId => let userFacingName := (← getLCtx).get! fvarId |>.userName
                   return leaf userFacingName.toString
  | mvar mvarId => return leaf mvarId.name.toString 
  | lit x => match x with 
             | .natVal n => return leaf (toString n)
             | .strVal s => return leaf s 
  | sort _ => return none 
  | app f x => do
      match f with 
      | .const c _ => 
        if (← isInstance c) then 
          dbg_trace "Found instance constant: {c}"
          return none
        else 
          let (function, arguments) := unfoldArguments (Expr.app f x)
          let argumentsAsTrees ← arguments.mapM Expr.toDisplayTree 
          let label := (← ppExpr function).pretty
          DisplayAlias.addLabel label
          return node label argumentsAsTrees.reduceOption  
      | _ => 
        let (function, arguments) := unfoldArguments (Expr.app f x)
        let argumentsAsTrees ← arguments.mapM Expr.toDisplayTree 
        let label := (← ppExpr function).pretty
        DisplayAlias.addLabel label
        return node label argumentsAsTrees.reduceOption  
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
