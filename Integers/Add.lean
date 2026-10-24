import Naturals.Add
import Integers.Neg

open ℕ (zero succ)

namespace ℤ

/-- `m - n` as an integer. -/
def subNatNat : ℕ → ℕ → ℤ
  | m, zero => ofNat m
  | zero, succ n => negSucc n
  | succ m, succ n => subNatNat m n

/-- Addition, by cases on both signs. Mixed signs reduce to `subNatNat`. -/
def add : ℤ → ℤ → ℤ
  | ofNat m, ofNat n => ofNat (m + n)
  | ofNat m, negSucc n => subNatNat m (succ n)
  | negSucc m, ofNat n => subNatNat n (succ m)
  | negSucc m, negSucc n => negSucc (succ (m + n))

/-- Lets `a + b` stand for `add a b`. -/
instance : Add ℤ := ⟨add⟩

/-- `1 + (-2) = -1` -/
example : ofNat (succ zero) + negSucc (succ zero) = negSucc zero := rfl

/-- `ofNat m + ofNat n = ofNat (m + n)` -/
theorem ofNat_add_ofNat (m n : ℕ) : ofNat m + ofNat n = ofNat (m + n) := rfl

/-- `-(m + 1) + -(n + 1) = -((m + n + 1) + 1)` -/
theorem negSucc_add_negSucc (m n : ℕ) :
    negSucc m + negSucc n = negSucc (succ (m + n)) := rfl

/-- `(m + 1) - (n + 1) = m - n` for `subNatNat` -/
theorem subNatNat_succ_succ (m n : ℕ) : subNatNat (succ m) (succ n) = subNatNat m n := rfl

/-- `a + 0 = a` -/
theorem add_zero (a : ℤ) : a + ofNat zero = a := by
  cases a with
  | ofNat n => rfl
  | negSucc n => rfl

/-- `a + b = b + a`

`ℕ.add_comm` needs its prefix because inside `namespace ℤ`, `add_comm` is this theorem. -/
theorem add_comm (a b : ℤ) : a + b = b + a := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [
        ofNat_add_ofNat,
        ofNat_add_ofNat,
        ℕ.add_comm
      ]
    | negSucc n => rfl
  | negSucc m =>
    cases b with
    | ofNat n => rfl
    | negSucc n =>
      rw [
        negSucc_add_negSucc,
        negSucc_add_negSucc,
        ℕ.add_comm
      ]

/-- `n - n = 0` for `subNatNat`

The `induction` tactic builds the same recursive proof that `Naturals` writes by hand. -/
theorem subNatNat_self (n : ℕ) : subNatNat n n = ofNat zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      subNatNat_succ_succ,
      ih
    ]

-- The term that `induction` and `rw` built. `ℕ.rec` takes the base case and a step function
-- `fun n ih => ...`, so `ih` is an argument, as in `Naturals`. Each `rw` became a `congrArg`.
#print subNatNat_self

/-- `-a + a = 0` -/
theorem neg_add_cancel (a : ℤ) : -a + a = ofNat zero := by
  -- Exercise. Split into cases as `neg_neg` does. Some cases hold by computation (`rfl`).
  -- The others compute to `subNatNat k k = ofNat zero` for some `k`. State that form with
  -- `show subNatNat k k = ofNat zero`, then try `exact?`: it searches every lemma in scope,
  -- including the ones proved earlier in this file.
  sorry

end ℤ
