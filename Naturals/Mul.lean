import Naturals.Add

namespace ℕ

/-- Multiplication, by recursion on the second argument. -/
def mul : ℕ → ℕ → ℕ
  | _, zero => zero
  | m, succ n => mul m n + m

/-- Lets `m * n` stand for `mul m n`. -/
instance : Mul ℕ := ⟨mul⟩

/-- `m · 0 = 0` -/
theorem mul_zero (m : ℕ) : m * zero = zero := rfl

/-- `m · (n + 1) = m · n + m` -/
theorem mul_succ (m n : ℕ) : m * succ n = m * n + m := rfl

/-- `0 · n = 0` -/
theorem zero_mul : (n : ℕ) → zero * n = zero
  | zero => rfl
  | succ n => zero_mul n

/-- `(m + 1) · n = m · n + n`

* `calc` chains equations, each with its own proof. Steps proved by `rfl` hold by computation.
* `congrArg (fun x => succ (x + m)) h` uses `h` inside the expression `succ (_ + m)`. -/
theorem succ_mul : (m n : ℕ) → succ m * n = m * n + n
  | _, zero => rfl
  | m, succ n =>
    calc succ m * succ n
        = succ (succ m * n + m) := rfl
      _ = succ (m * n + n + m) := congrArg (fun x => succ (x + m)) (succ_mul m n)
      _ = succ (m * n + (n + m)) := congrArg succ (add_assoc (m * n) n m)
      _ = succ (m * n + (m + n)) := congrArg (fun x => succ (m * n + x)) (add_comm n m)
      _ = succ (m * n + m + n) := congrArg succ (add_assoc (m * n) m n).symm
      _ = m * succ n + succ n := rfl

/-- `m · n = n · m` -/
theorem mul_comm : (m n : ℕ) → m * n = n * m
  | m, zero => (zero_mul m).symm
  | m, succ n =>
    calc m * succ n
        = m * n + m := rfl
      _ = n * m + m := congrArg (fun x => x + m) (mul_comm m n)
      _ = succ n * m := (succ_mul n m).symm

/-- `a · (b + c) = a · b + a · c` -/
theorem mul_add : (a b c : ℕ) → a * (b + c) = a * b + a * c
  | _, _, zero => rfl
  | a, b, succ c =>
    calc a * (b + succ c)
        = a * (b + c) + a := rfl
      _ = a * b + a * c + a := congrArg (fun x => x + a) (mul_add a b c)
      _ = a * b + (a * c + a) := add_assoc (a * b) (a * c) a

end ℕ
