import Naturals.Add

namespace ℕ

/-- The predecessor, with `pred 0 = 0`. -/
def pred : ℕ → ℕ
  | zero => zero
  | succ n => n

/-- Truncated subtraction: `m - n = 0` whenever `n ≥ m`.

Junk values keep operations total, and theorems carry the hypotheses instead.
Core Lean's `Nat` works the same way. -/
def sub : ℕ → ℕ → ℕ
  | m, zero => m
  | m, succ n => pred (sub m n)

/-- Lets `m - n` stand for `sub m n`. -/
instance : Sub ℕ := ⟨sub⟩

/-- `1 - 2 = 0` -/
example : succ zero - succ (succ zero) = zero := rfl

/-- `m - 0 = m` -/
theorem sub_zero (m : ℕ) : m - zero = m := rfl

/-- `m - (n + 1) = pred (m - n)` -/
theorem sub_succ (m n : ℕ) : m - succ n = pred (m - n) := rfl

/-- `0 - n = 0` -/
theorem zero_sub : (n : ℕ) → zero - n = zero
  | zero => rfl
  | succ n => congrArg pred (zero_sub n)

/-- `(m + 1) - (n + 1) = m - n` -/
theorem succ_sub_succ (m : ℕ) : (n : ℕ) → succ m - succ n = m - n
  | zero => rfl
  | succ n => congrArg pred (succ_sub_succ m n)

/-- `(m + n) - n = m` -/
theorem add_sub_cancel (m : ℕ) : (n : ℕ) → m + n - n = m
  | zero => rfl
  | succ n => (succ_sub_succ (m + n) n).trans (add_sub_cancel m n)

end ℕ
