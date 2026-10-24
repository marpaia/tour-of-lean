import Naturals.Basic

namespace ℕ

/-- Addition, by recursion on the second argument.

`ℕ → ℕ → ℕ` means `ℕ → (ℕ → ℕ)`: `add m` is the function `n ↦ m + n`. -/
def add : ℕ → ℕ → ℕ
  | m, zero => m
  | m, succ n => succ (add m n)

/-- Lets `m + n` stand for `add m n`. -/
instance : Add ℕ := ⟨add⟩

/-- `1 + 1 = 2` -/
example : succ zero + succ zero = succ (succ zero) := rfl

/-- `m + 0 = m` -/
theorem add_zero (m : ℕ) : m + zero = m := rfl

/-- `m + (n + 1) = (m + n) + 1` -/
theorem add_succ (m n : ℕ) : m + succ n = succ (m + n) := rfl

/-- `0 + n = n`

* A proof by induction is a recursive function, defined by pattern matching like `add`.
  The recursive call `zero_add n` is the induction hypothesis.
* `congrArg f h` turns a proof `h : a = b` into a proof of `f a = f b`. -/
theorem zero_add : (n : ℕ) → zero + n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add n)

/-- `(m + 1) + n = (m + n) + 1` -/
theorem succ_add : (m n : ℕ) → succ m + n = succ (m + n)
  | _, zero => rfl
  | m, succ n => congrArg succ (succ_add m n)

/-- `m + n = n + m`

`h.symm` reverses an equation `h`, and `h₁.trans h₂` chains `a = b` and `b = c` into `a = c`. -/
theorem add_comm : (m n : ℕ) → m + n = n + m
  | m, zero => (zero_add m).symm
  | m, succ n => (congrArg succ (add_comm m n)).trans (succ_add n m).symm

/-- `(a + b) + c = a + (b + c)` -/
theorem add_assoc : (a b c : ℕ) → a + b + c = a + (b + c) :=
  -- Exercise. `add` recurses on its second argument, so recurse on `c`.
  -- `succ_add` shows how to match on several arguments at once, and `zero_add` has the same shape.
  sorry

end ℕ
