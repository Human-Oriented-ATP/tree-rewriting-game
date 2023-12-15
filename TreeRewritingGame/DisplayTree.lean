import ProofWidgets 
import Std.Data.Array.Basic
import TreeRewritingGame.DisplayAliasExtension

open Lean Meta Widget

instance : Repr CodeWithInfos where
  reprPrec c _prec := c.pretty

inductive DisplayTree where 
  | node: (label : CodeWithInfos) → (children: Array DisplayTree) → DisplayTree
deriving Repr

open DisplayTree

def DisplayTree.leaf (label : CodeWithInfos) := node label #[]

#mkrpcenc DisplayTree

partial def DisplayTree.withAliases : DisplayTree → CoreM DisplayTree 
  | node label children => do 
    let alias_ := match (← DisplayAlias.getAlias? label.pretty) with 
      | some alias_ => .text alias_ -- TODO : This is not the ideal way of restoring the label
      | none => label 
    pure (node alias_ (← children.mapM DisplayTree.withAliases)) 

def unfoldArguments : Expr → Expr × Array Expr
  | Expr.app f x => let (function, arguments) := unfoldArguments f
                    (function, arguments ++ #[x]) 
  | e => (e, #[])

open Expr in 
partial def Lean.Expr.toDisplayTree (e : Expr) : MetaM (Option DisplayTree) := do 
  match e with 
  | e@(const ..) => let label ← ppExprTagged e
                    DisplayAlias.addLabel label.pretty
                    return leaf label
  | e@(fvar ..)
  | e@(mvar ..)
  | e@(lit ..) => return leaf (← ppExprTagged e) 
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
          let label ← ppExprTagged function
          DisplayAlias.addLabel label.pretty
          return node label argumentsAsTrees.reduceOption  
      | _ => 
        let (function, arguments) := unfoldArguments (Expr.app f x)
        let argumentsAsTrees ← arguments.mapM Expr.toDisplayTree 
        let label ← ppExprTagged function
        DisplayAlias.addLabel label.pretty
        return node label argumentsAsTrees.reduceOption  
  | e@(Expr.forallE ..) =>
      Meta.forallTelescopeReducing e (fun fvars body => do
      let isDependent := body.hasAnyFVar (fun f => fvars.contains (fvar f))
      let bodyAsTree ← body.toDisplayTree
      if isDependent then
        let fvarsAsTrees ← fvars.mapM Expr.toDisplayTree
        return node (.text "∀") (fvarsAsTrees ++ #[bodyAsTree]).reduceOption
      else 
        let fvarTypes ← fvars.mapM inferType
        let fvarTypesAsTrees ← fvarTypes.mapM Expr.toDisplayTree
        return node (.text "→") (fvarTypesAsTrees ++ #[bodyAsTree]).reduceOption  
      )
  | e@(Expr.lam ..) => 
      lambdaTelescope e (fun fvars body => do
      let bodyTree ← body.toDisplayTree
      let fvarsAsTrees ← fvars.mapM Expr.toDisplayTree
      return node (.text "λ") (fvarsAsTrees ++ #[bodyTree]).reduceOption
      )
  | Expr.bvar _ => panic! "Unbound bvar in expression"
  | Expr.mdata _ e => e.toDisplayTree
  | Expr.letE .. => panic! "Unreduced let in expression"
  | Expr.proj .. => return none
