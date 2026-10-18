set_option pp.fieldNotation false

inductive ℕ where
  | zero : ℕ
  | succ (n : ℕ) : ℕ

namespace ℕ

def add : ℕ → ℕ → ℕ
  | m, zero => m
  | m, succ n => succ (add m n)

instance : Add ℕ := ⟨add⟩

example : succ zero + succ zero = succ (succ zero) := rfl

theorem add_zero (m : ℕ) : m + zero = m := rfl

theorem add_succ (m n : ℕ) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : ℕ) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      add_succ,
      ih
    ]

theorem succ_add (m n : ℕ) : succ m + n = succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      add_succ,
      ih,
      add_succ
    ]

theorem add_comm (m n : ℕ) : m + n = n + m := by
  induction n with
  | zero =>
    rw [
      add_zero,
      zero_add
    ]
  | succ n ih =>
    rw [
      add_succ,
      succ_add,
      ih
    ]

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [
      add_succ,
      add_succ,
      add_succ,
      ih
    ]

def Even (n : ℕ) : Prop := ∃ k, n = k + k

theorem even_zero : Even zero := ⟨zero, rfl⟩

theorem even_add (m n : ℕ) (hm : Even m) (hn : Even n) : Even (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  refine ⟨a + b, ?_⟩
  rw [
    ha,
    hb
  ]
  calc a + a + (b + b)
      = a + (a + (b + b)) := by rw [add_assoc]
    _ = a + (a + b + b) := by rw [add_assoc a b b]
    _ = a + (b + a + b) := by rw [add_comm a b]
    _ = a + (b + (a + b)) := by rw [add_assoc b a b]
    _ = a + b + (a + b) := by rw [add_assoc]

end ℕ
