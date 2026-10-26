/- `a + b + c = a + (c + b)` -/

theorem add_add_swap (a b c : Nat) : a + b + c = a + (c + b) :=
  (Nat.add_assoc a b c).trans (congrArg (a + ·) (Nat.add_comm b c))

theorem add_add_swap_tactics(a b c : Nat) : a + b + c = a + (c + b) := by
  rw [
    Nat.add_assoc,
    Nat.add_comm b c
  ]

/-- `a + b = b + a ∧ a * b = b * a` -/

theorem add_mul_comm (a b : Nat) : a + b = b + a ∧ a * b = b * a :=
  ⟨Nat.add_comm a b, Nat.mul_comm a b⟩

theorem add_mul_comm_tactics (a b : Nat) : a + b = b + a ∧ a * b = b * a := by
  constructor
  · rw [Nat.add_comm]
  · rw [Nat.mul_comm]

/-- `0 + n = n` -/

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      Nat.add_succ,
      ih
    ]
