import TreeRewritingGame.TreeDisplay

def T₀ := Nat
def A : T₀ → T₀ → T₀ := Nat.add

def problem (x y z : T₀) : Prop := A x (A y z) = A (A y x) z

def l0 : A x y = A y x := by 
  rw [A] ; apply Nat.add_comm

def l1 : A (A x y) z = A x (A y z) := by 
  rw [A] ; apply Nat.add_assoc

def library : Array Lean.Name := #[
  `l0, 
  `l1
]

-- In this file for testing purposes
example (x y z : T₀) : problem x y z := by 
  rw [problem]
  with_panel_widgets[ProofWidgets.GoalTypePanel]
  sorry
