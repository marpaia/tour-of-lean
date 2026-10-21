import Naturals.Add

namespace ℕ

/-- The predecessor, with `pred 0 = 0`.

Lean functions are total, so `0` gets a junk value instead of being excluded. -/
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

/-- `1 - 2 = 0`, by computation. -/
example : succ zero - succ (succ zero) = zero := rfl

/-- `m - 0 = m`, by definition. -/
theorem sub_zero (m : ℕ) : m - zero = m := rfl

/-- `m - (n + 1) = pred (m - n)`, by definition. -/
theorem sub_succ (m n : ℕ) : m - succ n = pred (m - n) := rfl

/-- `0 - n = 0`, by induction on `n`.

`congrArg pred` gives `pred (0 - n) = pred 0`, and `pred 0` computes to `0`. -/
theorem zero_sub : (n : ℕ) → zero - n = zero
  | zero => rfl
  | succ n => congrArg pred (zero_sub n)

/-- `(m + 1) - (n + 1) = m - n`, by induction on `n`. -/
theorem succ_sub_succ (m : ℕ) : (n : ℕ) → succ m - succ n = m - n
  | zero => rfl
  | succ n => congrArg pred (succ_sub_succ m n)

/-- `(m + n) - n = m`, by induction on `n`.

No hypothesis is needed, since truncation never applies. -/
theorem add_sub_cancel (m : ℕ) : (n : ℕ) → m + n - n = m
  | zero => rfl
  | succ n => (succ_sub_succ (m + n) n).trans (add_sub_cancel m n)

end ℕ
