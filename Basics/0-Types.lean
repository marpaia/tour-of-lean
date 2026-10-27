-- Every value has a type. `#check` shows it.
#check 2
#check "Fizz"
#check 2 + 2

-- Types are values too. `Nat : Type`, and `Type` itself has a type.
#check Nat
#check Type

/-- Doubles `n`. -/
def double (n : Nat) : Nat := 2 * n

-- `#check` shows a function's type, `#eval` runs it.
#check double
#eval double 21
#check fun n : Nat => n + 1
#check Nat → Nat

-- A statement is a type, of type `Prop`, and a proof is a value of that type.
#check 2 + 2 = 4
#check Prop

/-- `2 + 2 = 4`

`rfl` proves any equation whose two sides compute to the same value. -/
example : 2 + 2 = 4 := rfl

-- A dependent type: `Nat.add_zero 3 : 3 + 0 = 3`, so the type of `Nat.add_zero n` depends on `n`.
-- `∀ (n : Nat), n + 0 = n` is the type of functions sending each `n` to a proof about `n`,
-- and `(n : Nat) → n + 0 = n` is another spelling of it.
#check Nat.add_zero
#check Nat.add_zero 3
#check (n : Nat) → n + 0 = n
