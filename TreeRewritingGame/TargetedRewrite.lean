import Lean
import Qq

/-!

A version of Lean's `rewrite` tactic that rewrites at a given `SubExpr.Pos`.

This tactic is capable of rewriting under binders.

-/

open Lean Qq Elab Meta

def mkEqQ {α : Q(Sort u)} (x y : Q($α)) : MetaM Q($x = $y) :=
  mkEq x y

def mkEqReflQ {α : Q(Sort u)} (x : Q($α)) : MetaM Q($x = $x) :=
  mkEqRefl x

def replaceAtPos {α β : Q(Sort u)} (p : SubExpr.Pos) (lhs rhs : Q($α)) : Q($β) → MetaM Q($β) :=
  replaceSubexpr (p := p) fun e ↦ do
    unless (← isDefEq e lhs) do
      throwError m!"Sub-expression {e} does not match expected pattern {lhs}."
    return rhs

def rewriteAt (p : SubExpr.Pos) (e heq : Expr) (symm : Bool := false) : MetaM RewriteResult := do
  let heqType ← instantiateMVars =<< inferType heq
  let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
  let heq := mkAppN heq newMVars
  let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM (not <$> ·.isAssigned)
  let ⟨eUniv, eType, e⟩ ← inferTypeQ e 
  let contAt {u : Level} {α β : Q(Sort u)} {lhs rhs : Q($α)} (p : SubExpr.Pos) (heq : Q($lhs = $rhs)) (e : Q($β)) : MetaM RewriteResult := do
    let e ← instantiateMVarsQ e 
    let eNew ← instantiateMVarsQ =<< replaceAtPos p lhs rhs e
    let motive : Expr ← withLocalDeclQ `_a .default α fun a ↦ do
      let e' ← replaceSubexpr (p := p) (root := e) fun _ ↦ return a
      let eq ← mkEqQ e e' 
      Impl.mkLambdaQ `_a a eq
    unless (← isTypeCorrect motive) do
      throwError "motive is not type correct"
    let eqRefl ← mkEqReflQ e
    let eqPrf : Q($e = $eNew) ← mkEqNDRec motive eqRefl heq
    
    let otherMVarIds ← getMVarsNoDelayed eqPrf
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
  match heqType.eqOrIff? with
  | some (lhs, rhs) =>
      let α ← inferType lhs
      if symm then
        contAt (α := α) (lhs := rhs) (rhs := lhs) (p := p) (heq := ← mkEqSymm heq) e
      else
        contAt (α := α) (lhs := lhs) (rhs := rhs) (p := p) (heq := heq) e
  | none => throwError "Equality or iff expected"

open Tactic in
elab "rewrite" "[" symm:("←")? hyp:term "]" "at" "[" pos:num,* "]" : tactic => do
  let p : SubExpr.Pos := pos.getElems.map (·.raw.isNatLit?.get!) |> .ofArray
  let hyp : Expr ← Term.elabTerm hyp none
  let goal ← getMainGoal
  Term.withSynthesize <| goal.withContext do
    let target := (← goal.getDecl).type
    let r ← rewriteAt p target hyp symm.isSome
    let goal' ← goal.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (goal' :: r.mvarIds)

-- example : ∀ m n : Nat, m + n = n + m := by
--   rewrite [Nat.add_comm] at [1, 1, 0, 1]

example : ∀ f : Nat → Nat, f (1 + 2) = f (2 + 1) := by
  rewrite [Nat.add_comm] at [1, 0, 1, 1]
  sorry