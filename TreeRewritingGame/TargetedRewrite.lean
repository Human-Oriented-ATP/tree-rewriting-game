import Lean
import Qq

open Lean Qq Elab Meta

def mkEqQ {α : Q(Sort u)} (x y : Q($α)) : MetaM Q($x = $y) :=
  mkEq x y

def mkEqReflQ {α : Q(Sort u)} (x : Q($α)) : MetaM Q($x = $x) :=
  mkEqRefl x

def replaceAtPos {α β : Q(Sort u)} (p : SubExpr.Pos) (lhs rhs : Q($α)) : Q($β) → MetaM Q($β) :=
  replaceSubexpr (p := p) fun e ↦ do
    unless (← isDefEq e lhs) do
      throwError m!"Sub-expression does not match expected pattern."
    return rhs

def rewriteAt (p : SubExpr.Pos) (e heq : Expr) : MetaM RewriteResult := do
  let heqType ← instantiateMVars =<< inferType heq
  let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
  let heq := mkAppN heq newMVars
  let ⟨eUniv, eType, e⟩ ← inferTypeQ e 
  let contAt {u : Level} {α β : Q(Sort u)} {lhs rhs : Q($α)} (p : SubExpr.Pos) (heq : Q($lhs = $rhs)) (e : Q($β)) : MetaM RewriteResult := do
    let e ← instantiateMVarsQ e 
    let eNew ← instantiateMVarsQ =<< replaceAtPos p lhs rhs e
    let motive : Expr ← withLocalDeclQ `_a .default α fun a ↦ do
      let e' ← replaceAtPos p lhs a e
      let eq ← mkEqQ e e' 
      Impl.mkLambdaQ `_a a eq
    unless (← isTypeCorrect motive) do
      throwError "motive is not type correct"
    let eqRefl ← mkEqReflQ e
    let eqPrf : Q($e = $eNew) ← mkEqNDRec motive eqRefl heq
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM (not <$> ·.isAssigned)
    let otherMVarIds ← getMVarsNoDelayed eqPrf
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
  match heqType.eqOrIff? with
  | some (lhs, rhs) =>
      let α ← inferType lhs  
      contAt (α := α) (lhs := lhs) (rhs := rhs) (p := p) (heq := heq) e
  | none => throwError "Equality or iff expected"

open Tactic in
elab "rewrite" "[" hyp:name "]" "at" "[" pos:num,* "]" : tactic => do
  let p : SubExpr.Pos := pos.getElems.map (·.raw.isNatLit?.get!) |> .ofArray
  let hyp : Expr ← mkConstWithLevelParams hyp.getName
  let goal ← getMainGoal
  Term.withSynthesize <| goal.withContext do
    let target := (← goal.getDecl).type
    let r ← rewriteAt p target hyp
    let goal' ← goal.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (goal' :: r.mvarIds)