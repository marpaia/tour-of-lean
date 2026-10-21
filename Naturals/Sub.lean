import Naturals.Add

namespace ℕ

/-- Truncated subtraction: `m - n = 0` whenever `n ≥ m`.

Junk values keep operations total, and theorems carry the hypotheses instead.
Core Lean's `Nat` works the same way. -/
def sub : ℕ → ℕ → ℕ
  | m, zero => m
  | zero, succ _ => zero
  | succ m, succ n => sub m n

/-- Lets `m - n` stand for `sub m n`. -/
instance : Sub ℕ := ⟨sub⟩

/-- `1 - 2 = 0` -/
example : succ zero - succ (succ zero) = zero := rfl

/-- `m - 0 = m`

Unlike `add_zero`, this is not `rfl`. `sub` matches on `m` first,
so `m - 0` computes only once `m` is `zero` or `succ m`. -/
theorem sub_zero : (m : ℕ) → m - zero = m
  | zero => rfl
  | succ _ => rfl

/-- `0 - n = 0` -/
theorem zero_sub : (n : ℕ) → zero - n = zero
  | zero => rfl
  | succ _ => rfl

/-- `(m + 1) - (n + 1) = m - n` -/
theorem succ_sub_succ (m n : ℕ) : succ m - succ n = m - n := rfl

/-- `(m + n) - n = m` -/
theorem add_sub_cancel : (m n : ℕ) → m + n - n = m
  | m, zero => sub_zero m
  | m, succ n => add_sub_cancel m n

end ℕ
