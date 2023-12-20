import TreeRewritingGame.MaskedDisplay

@[reducible] 
def T0 := Nat

def problem (a b c : Nat) : Prop := a * (b - c) = a*b - a*c

def library : Array Lean.Name := #[
  `Nat.mul_sub_left_distrib
]

-- for testing purposes
example (x y z : T0) : problem x y z := by 
  rw [problem]
  rw [Nat.mul_sub_left_distrib]
