import Arithmetic.Naturals

set_option pp.fieldNotation false

namespace ℕ

def mul : ℕ → ℕ → ℕ
  | _, zero => zero
  | m, succ n => mul m n + m

instance : Mul ℕ := ⟨mul⟩

theorem mul_zero (m : ℕ) : m * zero = zero := rfl

theorem mul_succ (m n : ℕ) : m * succ n = m * n + m := rfl

theorem zero_mul (n : ℕ) : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      mul_succ,
      ih,
      add_zero
    ]

theorem succ_mul (m n : ℕ) : succ m * n = m * n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      mul_succ,
      mul_succ,
      ih,
      add_succ,
      add_succ,
      add_assoc,
      add_assoc,
      add_comm n m
    ]

theorem mul_comm (m n : ℕ) : m * n = n * m := by
  induction n with
  | zero =>
    rw [
      mul_zero,
      zero_mul
    ]
  | succ n ih =>
    rw [
      mul_succ,
      succ_mul,
      ih
    ]

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [
      add_zero,
      mul_zero,
      add_zero
    ]
  | succ c ih =>
    rw [
      add_succ,
      mul_succ,
      mul_succ,
      ih,
      add_assoc
    ]

end ℕ
