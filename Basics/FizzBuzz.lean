/-- `"Fizz"` when `3 ∣ n`, otherwise empty. -/
def fizz (n : Nat) : String :=
  if 3 ∣ n then "Fizz" else ""

/-- `"Buzz"` when `5 ∣ n`, otherwise empty. -/
def buzz (n : Nat) : String :=
  if 5 ∣ n then "Buzz" else ""

/-- The words for `n`, or `n` itself when there are none. -/
def fizzbuzz (n : Nat) : String :=
  if 3 ∣ n ∨ 5 ∣ n then fizz n ++ buzz n else toString n

#eval (List.range 16).map fizzbuzz

/-- `fizzbuzz 15 = "FizzBuzz"`

A unit test that is also a theorem. `rfl` works because `fizzbuzz 15` computes. -/
example : fizzbuzz 15 = "FizzBuzz" := rfl

/-- `3 ∣ n → fizz n = "Fizz"`

`fizz n` unfolds to an `if`, and `if_pos h` says an `if` whose condition holds is its `then` branch. -/
theorem fizz_of_dvd (n : Nat) (h : 3 ∣ n) : fizz n = "Fizz" :=
  if_pos h

/-- `5 ∣ n → buzz n = "Buzz"` -/
theorem buzz_of_dvd (n : Nat) (h : 5 ∣ n) : buzz n = "Buzz" :=
  -- Exercise. `buzz` has the same shape as `fizz`.
  sorry

/-- `15 ∣ n → fizzbuzz n = "FizzBuzz"`

* `have` names an intermediate fact. `Nat.dvd_mul_right 3 5 : 3 ∣ 3 * 5` is accepted as `3 ∣ 15`
  because `3 * 5` computes.
* `calc` chains equations, each with its own proof.
* `congrArg f h` turns a proof `h : a = b` into a proof of `f a = f b`. Here `f` is a `fun`
  that places the rewritten string inside `_ ++ _`. -/
theorem fizzbuzz_of_dvd (n : Nat) (h : 15 ∣ n) : fizzbuzz n = "FizzBuzz" :=
  have h3 : 3 ∣ n := Nat.dvd_trans (Nat.dvd_mul_right 3 5) h
  have h5 : 5 ∣ n := Nat.dvd_trans (Nat.dvd_mul_left 5 3) h
  calc fizzbuzz n
      = fizz n ++ buzz n := if_pos (Or.inl h3)
    _ = "Fizz" ++ buzz n := congrArg (fun s => s ++ buzz n) (fizz_of_dvd n h3)
    _ = "Fizz" ++ "Buzz" := congrArg (fun s => "Fizz" ++ s) (buzz_of_dvd n h5)
    _ = "FizzBuzz" := rfl
