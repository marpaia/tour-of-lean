/-- `"Fizz"` when `3 ∣ n`, otherwise empty. -/
def fizz (n : Nat) : String :=
  if 3 ∣ n then
    "Fizz"
  else
    ""

/-- `"Buzz"` when `5 ∣ n`, otherwise empty. -/
def buzz (n : Nat) : String :=
  if 5 ∣ n then
    "Buzz"
  else
    ""

/-- Fizz if 3 ∣ n, Buzz if 5 ∣ n, otherwise n -/
def fizzbuzz (n : Nat) : String :=
  if 3 ∣ n ∨ 5 ∣ n then
    fizz n ++ buzz n
  else
    toString n

#eval (List.range' 1 16).map fizzbuzz

/-- `fizzbuzz 15 = "FizzBuzz"` -/
example : fizzbuzz 15 = "FizzBuzz" := rfl

/-- `3 ∣ n → fizz n = "Fizz"` -/
theorem fizz_of_dvd (n : Nat) (h3 : 3 ∣ n) : fizz n = "Fizz" := by
  unfold fizz
  rw [if_pos h3]

/-- `5 ∣ n → buzz n = "Buzz"` -/
theorem buzz_of_dvd (n : Nat) (h5 : 5 ∣ n) : buzz n = "Buzz" := by
  sorry

/-- `15 ∣ n → fizzbuzz n = "FizzBuzz"` -/
theorem fizzbuzz_of_dvd (n : Nat) (h15 : 15 ∣ n) : fizzbuzz n = "FizzBuzz" := by
  have h3 : 3 ∣ n := Nat.dvd_trans (by decide) h15
  have h5 : 5 ∣ n := Nat.dvd_trans (by decide) h15
  unfold fizzbuzz
  rw [if_pos (Or.inl h3), fizz_of_dvd n h3, buzz_of_dvd n h5]
  rfl
