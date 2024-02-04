import ProofWidgets 
import Std.Data.Array.Basic
import TreeRewritingGame.DisplayAliasExtension

open Lean PrettyPrinter Delaborator Meta Widget

instance : Repr CodeWithInfos where
  reprPrec c _prec := c.pretty

inductive DisplayTree where 
  | node : (label : CodeWithInfos) → (children : Array DisplayTree) → DisplayTree
deriving Repr

open DisplayTree

def DisplayTree.leaf (label : CodeWithInfos) := node label #[]

#mkrpcenc DisplayTree

section LensNotation

-- From Jovan's Zulip thread https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Lens-like.20notation/near/409670188

syntax ident "%~" : term
syntax ident "%~" term : term
macro_rules
| `($n:ident %~ $f $x) => `({ $x with $n:ident := $f $x.$n })
| `($n:ident %~ $f) => `(fun x => { x with $n:ident := $f x.$n })
| `($n:ident %~) => `(fun f x => { x with $n:ident := f x.$n })

end LensNotation

open Lean.Widget in
def Lean.Widget.CodeWithInfos.withRelativePos (codeWithInfos : CodeWithInfos) (pos : SubExpr.Pos) : CodeWithInfos :=
  codeWithInfos.map <| subexprPos %~ (SubExpr.Pos.append pos)

def ppExprTaggedRelative (e : Expr) : (ReaderT SubExpr.Pos MetaM) CodeWithInfos := do
  return (← ppExprTagged e).withRelativePos (← read)

open Lean PrettyPrinter
def annotateAs (txt : String) (e : SubExpr) (pos : SubExpr.Pos := .root) (delab : Delab := delab) : MetaM CodeWithInfos := do
  let (_stx, infos) ← delabCore e.expr {} delab
  let .some info := infos.find? pos | throwError m!"Could not find info for the expression {e.expr}."
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  let subexprInfo : SubexprInfo := {
    info := .mk {
      ctx := ctx,
      info := info,
      children := .empty
    },
    subexprPos := e.pos
  }
  return .tag subexprInfo (.text txt)

def annotateCurrentAs (txt : String) (e : Expr) : (ReaderT SubExpr.Pos MetaM) CodeWithInfos := do
  annotateAs txt ⟨e, ← read⟩

open Expr in 
partial def Lean.Expr.toDisplayTree (e : Expr) : (ReaderT SubExpr.Pos MetaM) (Option DisplayTree) := do 
  match e with 
  | e@(const ..) => 
      let label ← ppExprTaggedRelative e
      return leaf label
  | e@(fvar ..)
  | e@(mvar ..)
  | e@(lit ..) => return leaf (← ppExprTaggedRelative e) 
  | sort _ => return none 
  | e@(app ..) =>
      withApp e fun f arguments ↦ do
        if let some c := f.constName? then
          if (← isInstance c) then
            logInfo m!"Found instance constant: {c}"
            return none
        let (label, argumentsAsTrees) ← displayApp f arguments
        return node label argumentsAsTrees.reduceOption   
  | e@(Expr.forallE ..) =>
      Meta.forallTelescopeReducing e <| fun fvars body => do
      let isDependent := body.hasAnyFVar (fvars.contains <| fvar ·)
      let quantifiers ← 
        if isDependent then
          pure fvars
        else
          fvars.mapM (inferType ·)
      let label ←
        if isDependent then
           annotateCurrentAs "∀" e
        else
          annotateCurrentAs "→" e
      let (quantifierTrees, bodyTree) ← displayBinders quantifiers.toList body
      return node label (quantifierTrees.concat bodyTree).toArray.reduceOption
  | e@(Expr.lam ..) =>
      lambdaTelescope e <| fun fvars body => do
        let (quantifierTrees, bodyTree) ← displayBinders fvars.toList body
        let label ← annotateCurrentAs "λ" e
        return node label (quantifierTrees.concat bodyTree).toArray.reduceOption
  | Expr.bvar _ => panic! "Unbound bvar in expression"
  | Expr.mdata _ e => e.toDisplayTree
  | Expr.letE .. => panic! "Unreduced let in expression"
  | Expr.proj .. => return none
where
  -- Possible TODO: Refactor using `pushNaryArg` and `pushNthBindingDomain`
  displayApp (f : Expr) (args : Array Expr) : (ReaderT SubExpr.Pos MetaM) (CodeWithInfos × Array (Option DisplayTree)) :=
    if args.isEmpty then do
      return (← ppExprTaggedRelative f, #[])
    else do
      let arg := args.back
      let argsRest := args.pop
      let argTree ← withReader (·.pushAppArg) arg.toDisplayTree
      let (fLabel, argTrees) ← withReader (·.pushAppFn) <| displayApp f argsRest
      return (fLabel, argTrees.push argTree)
  displayBinders (quantifiers : List Expr) (body : Expr) : (ReaderT SubExpr.Pos MetaM) (List (Option DisplayTree) × Option DisplayTree) := do
    match quantifiers with
    | [] => return ([], ← body.toDisplayTree)
    | headQuantifier :: quantifiersRest => do
      let headQuantifierTree ← withReader (·.pushBindingDomain) headQuantifier.toDisplayTree
      let (quantifierTrees, bodyTree) ← withReader (·.pushBindingBody) <| displayBinders quantifiersRest body
      return (headQuantifierTree :: quantifierTrees, bodyTree)