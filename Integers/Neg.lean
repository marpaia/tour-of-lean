import Integers.Basic

open ℕ (zero succ)

namespace ℤ

/-- Negation. `0` gets its own case because `-0` is `ofNat zero`, not a `negSucc`. -/
def neg : ℤ → ℤ
  | ofNat zero => ofNat zero
  | ofNat (succ n) => negSucc n
  | negSucc n => ofNat (succ n)

/-- Lets `-a` stand for `neg a`. -/
instance : Neg ℤ := ⟨neg⟩

/-- `-(-a) = a`, by cases matching the three cases of `neg`.

The first proof by tactics. After `by`, each command builds part of the proof term,
and the infoview shows what remains to be proved. -/
theorem neg_neg (a : ℤ) : -(-a) = a := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n => rfl
  | negSucc n => rfl

end ℤ
