# A first tour of Lean

Lean 4 for mathematicians. You already know the mathematics; this teaches the Lean. Three short files, read in order, go from `#check` and FizzBuzz to a proof by induction. They import nothing at all.

## Setup

1. Install Lean by following <https://lean-lang.org/install>. This installs `elan`, the Lean version manager, and the VS Code extension.
2. Clone this repository and, from its root, run `lake build` to check every file.
3. Open the folder in VS Code.

## Reading the files

Lean is meant to be read in the editor, with the **infoview** panel open. It shows what Lean knows at the cursor.

- **At a `#check` or `#eval`**, it shows the type of an expression, or the result of running it.
- **In a term** (`0-Types`, and the first half of each pair in `2-Proofs`), it shows the term's type, which is the statement that term proves.
- **In a tactic proof** (everything else), it shows the goal: hypotheses above the `⊢`, and what remains to prove below it. Step through line by line and watch each tactic change the goal.
- **Hover** over any name for its type and docstring. **Ctrl-click** (Cmd-click on macOS) jumps to its definition.

Every definition and theorem has a docstring stating what it says.

## Lean as a programming language

Lean is a functional programming language in which every value has a type, and types are values too. A statement like `2 + 2 = 4` is a type, and a proof of it is a value of that type. So a theorem about a program is just another definition:

```lean
def fizz (n : Nat) : String :=
  if 3 ∣ n then
    "Fizz"
  else
    ""

theorem fizz_of_dvd (n : Nat) (h3 : 3 ∣ n) : fizz n = "Fizz" := by
  unfold fizz
  rw [if_pos h3]
```

The type `∀ (n : Nat), n + 0 = n` depends on the value `n` it quantifies over. That is what makes Lean's type theory *dependent*, and it is why a theorem with a universal quantifier is a function from `n` to a proof about `n`.

`Nat` itself is an ordinary `inductive` type with two constructors, `zero` and `succ n`, and that one declaration gives induction for free. The `induction` tactic splits a goal into the two cases and names the induction hypothesis `ih`:

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      Nat.add_succ,
      ih
    ]
```

`rfl` proves `n + 0 = n`, which holds by computation, but not `0 + n = n`, which needs this induction.

| File | Proves | Introduces |
|---|---|---|
| [`0-Types`](Basics/0-Types.lean) | `2 + 2 = 4` | `#check`, `Type`, `Prop`, statements as types, dependent function types |
| [`1-Programs`](Basics/1-Programs.lean) | `15 ∣ n → fizzbuzz n = "FizzBuzz"` | `def`, `#eval`, `if`, `∣`, `rfl` as a unit test, `by`, `unfold`, `rw`, `if_pos`, `have`, `decide` |
| [`2-Proofs`](Basics/2-Proofs.lean) | `a + b + c = a + (c + b)` and `a + b = b + a ∧ a * b = b * a`, each proved twice, then `0 + n = n` | core lemmas like `Nat.add_comm`, `.trans`, `congrArg`, `⟨_, _⟩` for `∧`, then `rw` with a lemma, `constructor`, `induction` |

`2-Proofs` shows each fact as a term and again as a tactic script, so the two styles can be compared on facts too simple to get in the way.

## Where to go next

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): the standard tutorial for doing mathematics with Mathlib, Lean's library of formalized mathematics.
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/): search for a lemma by name or statement.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): the natural numbers built from scratch, as an interactive game with tactics.
