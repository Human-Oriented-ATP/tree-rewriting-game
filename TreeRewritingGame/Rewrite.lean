import Lean
import Std.Lean.Position
import TreeRewritingGame.Utils


/-!

# Point-and-click rewriting

This file defines a widget for making targeted rewrites by
pointing and clicking sub-expressions in the infoview.

Once a sub-expression is selected, a `rw` tactic call with
a configuration targeting the selected location is generated.

-/

open Lean Server Elab Meta Parser Tactic

section

/-- Convert `Occurrences` to a `String`. -/
instance : ToString Occurrences where
  toString := fun
    | .all => ".all"
    | .pos occs => s!".pos {occs}"
    | .neg occs => s!".neg {occs}"

/-- Convert a `Rewrite.Config` to a `String`.
    This instance is restricted to printing just the information about the occurrences. -/
instance : ToString Rewrite.Config where
  toString cfg :=
    "{ " ++ s!"occs := {cfg.occs}" ++ " }"

end

/-- Specialises the theorem to match the sub-expression at the given position
    and calculates its occurrence number in the whole expression. -/
def findRewriteOccurrence (thm : Expr) (symm : Bool)
    (position : SubExpr.Pos) (target : Expr) : MetaM (Nat × Expr) := do
  let stmt ← inferType thm
  let (vars, _, eqn) ← forallMetaTelescopeReducing stmt
  let .some (lhs, rhs) := eqn.eqOrIff? |
    panic! s!"Received {stmt}; equality or iff proof expected."
  let hs := if symm then rhs else lhs
  let occurrence ← findMatchingOccurrence position target hs
  let pattern := mkAppN thm <| ← vars.mapM instantiateMVars
  return (occurrence, pattern)

/-- Generates a rewrite tactic call with configuration from the arguments. -/
def rewriteTacticCall (loc : SubExpr.GoalsLocation) (goal : Widget.InteractiveGoal)
    (thmAbst : AbstractMVarsResult) (symm : Bool) : MetaM String := do
  let subExpr ← loc.toSubExpr
  let us ← thmAbst.paramNames.mapM <| fun _ ↦ mkFreshLevelMVar
  let thm := thmAbst.expr.instantiateLevelParamsArray thmAbst.paramNames us
  let (occurrence, pattern) ← findRewriteOccurrence thm symm subExpr.pos subExpr.expr
  let cfg : Rewrite.Config := { occs := .pos [occurrence] }
  let arg := Format.pretty <| ← ppExpr pattern
  return s!"rw (config := {cfg}) [{(if symm then "← " else "") ++ arg}]{loc.loc.render goal}"