# A first tour of Lean

A short tour of Lean 4 for mathematicians. It assumes you know the mathematics and teaches only the Lean.

The tour has three parts, and each adds one layer:

| Part | Builds | Adds |
|---|---|---|
| 1. Naturals | ℕ from scratch | what a proof *is*: proofs written directly as terms |
| 2. Integers | ℤ on top of ℕ | tactics, which build those terms interactively |
| 3. Geometry | Pythagoras and Cauchy–Schwarz | Mathlib, Lean's library of formalized mathematics |

Parts 1 and 2 use core Lean only, with nothing imported from outside this repository.

## Setup

1. Install Lean by following <https://lean-lang.org/install>. This installs `elan` (the Lean version manager) and the VS Code extension.
2. Clone this repository and run, from its root:

   ```sh
   lake exe cache get   # download prebuilt Mathlib, so it is not compiled locally
   lake build           # check every file
   ```

3. Open the folder in VS Code.

## How to read a file

Read the files in order, since each builds on the ones before. The **infoview** panel is the main way to read Lean. Proofs make much more sense there than on the page.

- **Part 1:** put the cursor on a term to see its type, which is the statement it proves.
- **Parts 2 and 3:** put the cursor in a tactic proof to see the goal. Hypotheses are above the `⊢`, and what remains to be proved is below it. Step line by line and watch each tactic change the goal. Long `rw` lists put one lemma per line so you can step through each rewrite.
- **Hover** over any name to see its type and docstring. **Ctrl-click** (Cmd-click on macOS) jumps to its definition.

Every definition and theorem has a docstring saying what it states, plus anything about the proof the code doesn't make clear.

## Part 1: Naturals, without tactics

A proof of `a = b` is a value of type `a = b`, and a proof by induction is a recursive function. Every proof in this part is written that way, directly.

**1. [`Naturals/Basic.lean`](Naturals/Basic.lean)**: ℕ as `zero` and `succ n` (that is, `n + 1`).

- `inductive` types, from which Lean derives the Peano axioms and induction

**2. [`Naturals/Add.lean`](Naturals/Add.lean)**: `0 + n = n`, commutativity, associativity.

- functions by pattern matching and recursion
- curried types: `ℕ → ℕ → ℕ` means `ℕ → (ℕ → ℕ)`
- `instance`, to give `+` a meaning
- `rfl`, for equations that hold by computation (`m + 0 = m`), unlike those that need proof (`0 + m = m`)
- induction as a recursive function
- `congrArg`, `.symm` and `.trans`, to build proofs from other proofs

**3. [`Naturals/Mul.lean`](Naturals/Mul.lean)**: `0 · n = 0`, commutativity, distributivity.

- `calc`, to chain equations
- `congrArg` with a `fun`, to use an equation inside a larger expression

**4. [`Naturals/Sub.lean`](Naturals/Sub.lean)**: truncated subtraction and `(m + n) - n = m`.

- junk values: `1 - 2 = 0` in ℕ, just as `x / 0 = 0` in ℝ, because Lean functions are total

## Part 2: Integers, with tactics

Tactics are commands after `by` that build the proof term step by step. Case analysis on signs makes these proofs long to write as terms, and tactics keep them readable.

**5. [`Integers/Basic.lean`](Integers/Basic.lean)**: ℤ as `ofNat n` (that is, `n`) and `negSucc n` (that is, `-(n + 1)`).

- constructors that take arguments of another type
- a representation with no quotient, the same as core Lean's `Int`

**6. [`Integers/Neg.lean`](Integers/Neg.lean)**: `-(-a) = a`.

- nested patterns such as `ofNat (succ n)`
- `open ℕ (zero succ)`, to use names from another namespace
- the first tactic proof, with `cases`

**7. [`Integers/Add.lean`](Integers/Add.lean)**: commutativity and `-a + a = 0`, which is what ℕ lacks.

- `rw`, the `induction` tactic, and `exact`
- pattern matching on two arguments at once
- stating defining equations as `rfl` lemmas so `rw` can use them

## Part 3: Geometry, with Mathlib

What is new is the library: thousands of lemmas, typeclasses that describe mathematical structure, and automation for routine algebra. Each file ends with an `example` that cites Mathlib's version of the result.

**8. [`Geometry/PythagoreanTheorem.lean`](Geometry/PythagoreanTheorem.lean)**: `⟪u, v⟫ = 0 ↔ ‖u + v‖² = ‖u‖² + ‖v‖²` in a real inner product space.

- `variable` with typeclass hypotheses: "let `F` be a real inner product space"
- `ring` and `linarith`, which automate the algebra Parts 1 and 2 did by hand
- `↔` with `constructor` and `intro`
- `rw ... at h`, to rewrite a hypothesis

**9. [`Geometry/CauchySchwarz.lean`](Geometry/CauchySchwarz.lean)**: `|⟪u, v⟫| ≤ ‖u‖ ‖v‖`, via the discriminant of a nonnegative quadratic.

- `have`, for intermediate claims
- applying a library theorem (`discrim_le_zero`) to your own hypothesis
- rewriting right to left with `←`
- `positivity`

## Where to go next

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): the standard tutorial for doing mathematics with Mathlib.
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/): search for a lemma by name or statement.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): the natural numbers in much greater depth, as an interactive game with tactics.
