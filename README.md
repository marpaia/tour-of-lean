# A first tour of Lean

A short tour of Lean 4 for mathematicians. It assumes you know the mathematics and teaches only the Lean.

There are two parts. **Arithmetic** builds the natural numbers from scratch in core Lean, with no library, to show how Lean works at a low level. **Geometry** then uses Mathlib, Lean's library of formalized mathematics, to prove two familiar results about inner product spaces. It shows what working with the library looks like.

## Setup

1. Install Lean by following <https://lean-lang.org/install>. This installs `elan` (the Lean version manager) and the VS Code extension.
2. Clone this repository and run, from its root:

   ```sh
   lake exe cache get   # download prebuilt Mathlib, so it is not compiled locally
   lake build           # check every file
   ```

3. Open the folder in VS Code.

## How to read a file

Open a file and click into a proof. The **infoview** panel shows the current goal: the hypotheses in scope above the `⊢`, and what remains to be proved below it. Move the cursor line by line and watch each tactic change the goal. This is the main way to read Lean. The proofs make much more sense in the infoview than on the page.

The files have no comments, so each one can be read whole at a glance. The list below says what each file proves and which Lean features it introduces. Read the files in order, since each builds on the ones before. Long `rw` lists put one lemma per line, so you can step through them one rewrite at a time in the infoview. Hover over any name to see its type and documentation. Ctrl-click (Cmd-click on macOS) jumps to its definition.

## Part 1: Arithmetic

Core Lean only. Nothing is imported.

1. **[`Arithmetic/Naturals.lean`](Arithmetic/Naturals.lean)**: the natural numbers, addition, and even numbers.
   - Proves: `0 + n = n`, commutativity and associativity of addition, and that the sum of two even numbers is even.
   - Learn: defining a type with `inductive`; functions by pattern matching and recursion; curried function types like `ℕ → ℕ → ℕ`; `instance` to give `+` a meaning; `theorem` and `example`; `rfl`, and the difference between equations that hold by computation and those that need proof; tactic proofs with `by`; `induction`; `rw`; propositions as types; proving `∃` with `⟨witness, proof⟩` and using it with `obtain`; `refine`; `calc`.

2. **[`Arithmetic/Multiplication.lean`](Arithmetic/Multiplication.lean)**: multiplication.
   - Proves: `0 * n = 0`, commutativity of multiplication, and distributivity.
   - Learn: `import` to build on an earlier file. Otherwise nothing new: this file is practice with the tools from file 1, and a quick check that they have sunk in.

## Part 2: Geometry

These files use Mathlib. The tactics are the same as in Part 1. What is new is the library: thousands of definitions and lemmas, typeclasses that describe mathematical structure, and automation for routine algebra. Each file ends with an `example` that proves the same statement by citing Mathlib's version directly.

3. **[`Geometry/PythagoreanTheorem.lean`](Geometry/PythagoreanTheorem.lean)**: the Pythagorean theorem in a real inner product space.
   - Proves: the expansion `‖u + v‖² = ‖u‖² + 2⟪u, v⟫ + ‖v‖²`, and from it `⟪u, v⟫ = 0 ↔ ‖u + v‖² = ‖u‖² + ‖v‖²`.
   - Learn: importing Mathlib; `variable` with typeclass hypotheses, Lean's way of saying "let `F` be a real inner product space"; rewriting with Mathlib lemmas; `ring`, which automates the bookkeeping Part 1 did by hand; `linarith`; `↔` with `constructor`; `intro` and `exact`; rewriting a hypothesis with `rw ... at h`; citing Mathlib's version of a result instead of proving it.

4. **[`Geometry/CauchySchwarz.lean`](Geometry/CauchySchwarz.lean)**: the Cauchy–Schwarz inequality `|⟪u, v⟫| ≤ ‖u‖ ‖v‖`, via the discriminant of a nonnegative quadratic.
   - Learn: `have` for intermediate claims; `∀` statements; using a lemma name as a complete proof; rewriting right to left with `←`; applying a library theorem (`discrim_le_zero`) to your own hypothesis; `positivity`.

## Where to go next

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): the standard tutorial for doing mathematics with Mathlib.
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/): search for a lemma by name or statement.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): Part 1 in much greater depth, as an interactive game.
