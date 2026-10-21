/-- The natural numbers: `zero`, and `succ n` for `n + 1`.

Lean derives the Peano axioms and induction from this declaration alone. -/
inductive ℕ where
  | zero : ℕ
  | succ (n : ℕ) : ℕ
