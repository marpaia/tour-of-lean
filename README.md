# A first tour of Lean

Lean 4 for mathematicians. You already know the mathematics; this teaches the Lean. Nine short files, read in order, go from defining ℕ to proving Cauchy–Schwarz with Mathlib.

| Part | Builds | New idea |
|---|---|---|
| 1. [Naturals](#part-1-naturals-without-tactics) | ℕ from scratch | a proof is a term, and induction is recursion |
| 2. [Integers](#part-2-integers-with-tactics) | ℤ on top of ℕ | tactics, which build those terms interactively |
| 3. [Geometry](#part-3-geometry-with-mathlib) | Pythagoras and Cauchy–Schwarz | Mathlib, Lean's library of formalized mathematics |

Each part adds one layer, so every new feature has a clear origin. Parts 1 and 2 import nothing at all.

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

- **In a term** (Part 1), it shows the term's type, which is the statement that term proves.
- **In a tactic proof** (Parts 2 and 3), it shows the goal: hypotheses above the `⊢`, and what remains to prove below it. Step through line by line and watch each tactic change the goal.
- **Hover** over any name for its type and docstring. **Ctrl-click** (Cmd-click on macOS) jumps to its definition.

Every definition and theorem has a docstring stating what it says, plus a note wherever the proof uses something new.

## Part 1: Naturals, without tactics

A proof of `a = b` is a value of type `a = b`, and a proof by induction is a recursive function. This part writes every proof that way, directly:

```lean
theorem zero_add : (n : ℕ) → zero + n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add n)
```

The `succ n` case calls `zero_add n`, which is the induction hypothesis.

| File | Proves | Introduces |
|---|---|---|
| 1. [`Basic`](Naturals/Basic.lean) | defines ℕ as `zero` and `succ n` | `inductive` types, which give the Peano axioms and induction for free |
| 2. [`Add`](Naturals/Add.lean) | `0 + n = n`, commutativity, associativity | recursion by pattern matching, curried types, `instance`, `rfl`, `congrArg`, `.symm`, `.trans` |
| 3. [`Mul`](Naturals/Mul.lean) | `0 · n = 0`, commutativity, distributivity | `calc`, and `congrArg` with a `fun` to rewrite inside an expression |
| 4. [`Sub`](Naturals/Sub.lean) | `(m + n) - n = m` | junk values: `1 - 2 = 0` in ℕ, because Lean functions are total |

`rfl` deserves a closer look in `Add`. It proves `m + 0 = m`, which holds by computation, but not `0 + m = m`, which needs induction.

## Part 2: Integers, with tactics

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
| 5. [`Basic`](Integers/Basic.lean) | defines ℤ as `ofNat n` (`n`) and `negSucc n` (`-(n + 1)`) | constructors with arguments, and a representation that needs no quotient |
| 6. [`Neg`](Integers/Neg.lean) | `-(-a) = a` | the first tactic proof, `cases`, nested `cases`, `open` |
| 7. [`Add`](Integers/Add.lean) | commutativity, and `-a + a = 0`, which ℕ lacks | `rw`, `induction`, `exact` |

## Part 3: Geometry, with Mathlib

The tactics are the same as in Part 2. What is new is the library: thousands of lemmas, typeclasses that describe mathematical structure, and automation for routine algebra. Each file ends by citing Mathlib's own version of its result.

| File | Proves | Introduces |
|---|---|---|
| 8. [`PythagoreanTheorem`](Geometry/PythagoreanTheorem.lean) | `⟪u, v⟫ = 0 ↔ ‖u + v‖² = ‖u‖² + ‖v‖²` | `variable` to say "let `F` be a real inner product space", `ring`, `linarith`, `constructor`, `rw ... at h` |
| 9. [`CauchySchwarz`](Geometry/CauchySchwarz.lean) | `\|⟪u, v⟫\| ≤ ‖u‖ ‖v‖`, via the discriminant | importing your own file to reuse `norm_add_sq`, `have`, applying a library theorem to your own hypothesis, `←`, `positivity` |

## Where to go next

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): the standard tutorial for doing mathematics with Mathlib.
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/): search for a lemma by name or statement.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): the natural numbers in much greater depth, as an interactive game with tactics.
