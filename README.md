# A first tour of Lean

Lean 4 for mathematicians. You already know the mathematics; this teaches the Lean. Eleven short files, read in order, go from `#check` and FizzBuzz to proving Cauchy–Schwarz with Mathlib.

| Part | Builds | New idea |
|---|---|---|
| 1. [Basics](#part-1-basics-lean-as-a-programming-language) | FizzBuzz, and a theorem about it | Lean is a programming language, and a statement is a type |
| 2. [Naturals](#part-2-naturals-without-tactics) | ℕ from scratch | a proof is a term, and induction is recursion |
| 3. [Integers](#part-3-integers-with-tactics) | ℤ on top of ℕ | tactics, which build those terms interactively |
| 4. [Geometry](#part-4-geometry-with-mathlib) | Pythagoras and Cauchy–Schwarz | Mathlib, Lean's library of formalized mathematics |

Each part adds one layer, so every new feature has a clear origin. Parts 1 to 3 import nothing at all.

## Setup

1. Install Lean by following <https://lean-lang.org/install>. This installs `elan`, the Lean version manager, and the VS Code extension.
2. Clone this repository and, from its root, run:

   ```sh
   lake exe cache get   # download prebuilt Mathlib instead of compiling it
   lake build           # check every file
   ```

3. Open the folder in VS Code.

## Reading the files

Lean is meant to be read in the editor, with the **infoview** panel open. It shows what Lean knows at the cursor.

- **At a `#check` or `#eval`** (Part 1), it shows the type of an expression, or the result of running it.
- **In a term** (Parts 1 and 2), it shows the term's type, which is the statement that term proves.
- **In a tactic proof** (Parts 3 and 4), it shows the goal: hypotheses above the `⊢`, and what remains to prove below it. Step through line by line and watch each tactic change the goal.
- **Hover** over any name for its type and docstring. **Ctrl-click** (Cmd-click on macOS) jumps to its definition.

Every definition and theorem has a docstring stating what it says, plus a note wherever the proof uses something new.

## Part 1: Basics, Lean as a programming language

Lean is a functional programming language in which every value has a type, and types are values too. A statement like `2 + 2 = 4` is a type, and a proof of it is a value of that type. So a theorem about a program is just another definition:

```lean
def fizz (n : Nat) : String :=
  if 3 ∣ n then "Fizz" else ""

theorem fizz_of_dvd (n : Nat) (h : 3 ∣ n) : fizz n = "Fizz" := if_pos h
```

The type `∀ (n : Nat), n + 0 = n` depends on the value `n` it quantifies over. That is what makes Lean's type theory *dependent*, and it is why a theorem with a universal quantifier is a function from `n` to a proof about `n`.

| File | Proves | Introduces |
|---|---|---|
| 1. [`Types`](Basics/Types.lean) | `2 + 2 = 4` | `#check`, `Type`, `Prop`, statements as types, dependent function types |
| 2. [`FizzBuzz`](Basics/FizzBuzz.lean) | `15 ∣ n → fizzbuzz n = "FizzBuzz"` | `def`, `#eval`, `if`, `∣`, `rfl` as a unit test, `if_pos`, `have`, `calc`, `congrArg` |

This part uses Lean's built-in `Nat`. Part 2 rebuilds it from scratch to see what is inside.

## Part 2: Naturals, without tactics

A proof of `a = b` is a value of type `a = b`, and a proof by induction is a recursive function. This part writes every proof that way, directly:

```lean
theorem zero_add : (n : ℕ) → zero + n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add n)
```

The `succ n` case calls `zero_add n`, which is the induction hypothesis.

| File | Proves | Introduces |
|---|---|---|
| 3. [`Basic`](Naturals/Basic.lean) | defines ℕ as `zero` and `succ n` | `inductive` types, which give the Peano axioms and induction for free |
| 4. [`Add`](Naturals/Add.lean) | `0 + n = n`, commutativity, associativity | recursion by pattern matching, curried types, `instance`, `.symm`, `.trans` |
| 5. [`Mul`](Naturals/Mul.lean) | `0 · n = 0`, commutativity, distributivity | `calc` and `congrArg` again, now chaining recursive calls |
| 6. [`Sub`](Naturals/Sub.lean) | `(m + n) - n = m` | junk values: `1 - 2 = 0` in ℕ, because Lean functions are total |

`rfl` deserves a closer look in `Add`. It proves `m + 0 = m`, which holds by computation, but not `0 + m = m`, which needs induction.

## Part 3: Integers, with tactics

Tactics are commands, written after `by`, that build the proof term for you while the infoview shows what is left. Compare this induction with the one above:

```lean
theorem subNatNat_self (n : ℕ) : subNatNat n n = ofNat zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      subNatNat_succ_succ,
      ih
    ]
```

The proof has the same shape, but the induction hypothesis is now named `ih`, and `rw` does the rewriting. Proofs about ℤ split into cases by sign, and tactics keep them readable.

| File | Proves | Introduces |
|---|---|---|
| 7. [`Basic`](Integers/Basic.lean) | defines ℤ as `ofNat n` (`n`) and `negSucc n` (`-(n + 1)`) | constructors with arguments, and a representation that needs no quotient |
| 8. [`Neg`](Integers/Neg.lean) | `-(-a) = a` | the first tactic proof, `cases`, nested `cases`, `open` |
| 9. [`Add`](Integers/Add.lean) | commutativity, and `-a + a = 0`, which ℕ lacks | `rw`, `induction`, `exact` |

## Part 4: Geometry, with Mathlib

The tactics are the same as in Part 3. What is new is the library: thousands of lemmas, typeclasses that describe mathematical structure, and automation for routine algebra. Each file ends by citing Mathlib's own version of its result.

| File | Proves | Introduces |
|---|---|---|
| 10. [`PythagoreanTheorem`](Geometry/PythagoreanTheorem.lean) | `⟪u, v⟫ = 0 ↔ ‖u + v‖² = ‖u‖² + ‖v‖²` | `variable` to say "let `F` be a real inner product space", `ring`, `linarith`, `constructor`, `rw ... at h` |
| 11. [`CauchySchwarz`](Geometry/CauchySchwarz.lean) | `\|⟪u, v⟫\| ≤ ‖u‖ ‖v‖`, via the discriminant | importing your own file to reuse `norm_add_sq`, applying a library theorem to your own hypothesis, `←`, `positivity` |

## Where to go next

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): the standard tutorial for doing mathematics with Mathlib.
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/): search for a lemma by name or statement.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): the natural numbers in much greater depth, as an interactive game with tactics.
