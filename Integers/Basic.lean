import Naturals.Basic

/-- The integers: `ofNat n` is `n`, and `negSucc n` is `-(n + 1)`.

Each integer has exactly one representation, so no quotient is needed.
Core Lean's `Int` is defined the same way. -/
inductive ℤ where
  | ofNat (n : ℕ) : ℤ
  | negSucc (n : ℕ) : ℤ
