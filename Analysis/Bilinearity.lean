/-
# Bilinearity of the real inner product

Every proof in this directory that expands a squared length — the Pythagorean
theorem, the parallelogram law, Cauchy–Schwarz, the triangle inequality — runs
on the same engine: the inner product is *bilinear*. This file is the one place
that engine is laid out on its own, so the theorem files can name the laws and
get on with their argument. It proves nothing new; it is a reference sheet for
the algebra the expansions use.

## What bilinearity means

The inner product `⟪·, ·⟫_ℝ : F × F → ℝ` takes **two** vectors and returns a
scalar. It is **bilinear**: linear in each of its two slots separately, while
the other slot is held fixed. That is two laws per slot —

  * **additivity** — a sum in one slot splits into a sum of inner products;
  * **homogeneity** — a scalar in one slot factors out as ordinary
    multiplication.

Two slots times two laws is the whole of bilinearity. Written out for the left
slot (the right slot is the mirror image):

    ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫              ⟪c • x, z⟫ = c · ⟪x, z⟫

Subtraction is not a third law: it is additivity composed with negation. Mathlib
still packages that combination as its own rewrite (`inner_sub_left`), because a
difference is what the expansions most often reach for, so it is listed below
alongside the addition form.

## Why "bi", and why it forces a quadratic

Bilinear is *not* the same as linear in both arguments at once. Watch a single
scalar applied to both slots:

    ⟪c • x, c • y⟫ = c · ⟪x, c • y⟫ = c · c · ⟪x, y⟫ = c² · ⟪x, y⟫

The scalar comes out once per slot, so it lands *squared*. This is exactly why
the inner product behaves like a *product* of vectors — it distributes over
addition and lets scalars through, just like `·` — and why `⟪w, w⟫`, with `w`
filling both slots, expands to a **quadratic** the moment `w` is a combination
of other vectors. Pushing a self inner product through these laws is how each
theorem in this directory turns a statement about lengths into a polynomial that
`ring` or `nlinarith` can finish.

## How to read this file

Each law is exhibited as an `example` whose proof term *is* the Mathlib lemma
the proofs cite — so the name you read here (`inner_add_left`,
`real_inner_smul_right`, …) is the exact name to reach for, and to look up,
anywhere else. Nothing here is exported and nothing is renamed: the theorem
files import Mathlib and call these lemmas directly, by these names.

## The setting

We fix an arbitrary real inner-product space `F`:

  * `[NormedAddCommGroup F]` — vectors add, negate, and carry a norm `‖·‖`;
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Analysis.Bilinearity

/-! We fix an arbitrary real inner-product space `F` for the whole file, exactly
as the theorem files do, so the laws below are stated in the same setting they
are used. -/
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Additivity

A sum in either slot distributes across the inner product. These are the two
laws the expansions use to turn `⟪u ± v, ·⟫` into separate pairings. -/

-- Additivity, left slot.
example (x y z : F) : ⟪x + y, z⟫_ℝ = ⟪x, z⟫_ℝ + ⟪y, z⟫_ℝ := inner_add_left x y z

-- Additivity, right slot.
example (x y z : F) : ⟪x, y + z⟫_ℝ = ⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ := inner_add_right x y z

/-! ### Subtraction form

The same additivity, read through negation. A difference in either slot splits
the same way, carrying the minus sign along. These are the forms the diagonals
of the parallelogram and the `u - t • v` of Cauchy–Schwarz are expanded with. -/

-- Subtraction, left slot.
example (x y z : F) : ⟪x - y, z⟫_ℝ = ⟪x, z⟫_ℝ - ⟪y, z⟫_ℝ := inner_sub_left x y z

-- Subtraction, right slot.
example (x y z : F) : ⟪x, y - z⟫_ℝ = ⟪x, y⟫_ℝ - ⟪x, z⟫_ℝ := inner_sub_right x y z

/-! ### Homogeneity

A real scalar in either slot factors straight out as ordinary multiplication.
Note the argument order of the Mathlib lemmas: the two vectors come first and
the scalar last. This is the law that pulls the projection coefficient `t` out
of `⟪u - t • v, u - t • v⟫` in the Cauchy–Schwarz proof, where it duly appears
squared. -/

-- Homogeneity, left slot.
example (c : ℝ) (x y : F) : ⟪c • x, y⟫_ℝ = c * ⟪x, y⟫_ℝ := real_inner_smul_left x y c

-- Homogeneity, right slot.
example (c : ℝ) (x y : F) : ⟪x, c • y⟫_ℝ = c * ⟪x, y⟫_ℝ := real_inner_smul_right x y c

/-! ### Companion: symmetry

Symmetry is **not** part of bilinearity — it is a separate property — but the
expansions lean on it in the same breath, so it earns a place on the sheet.
Swapping the two slots of a *real* inner product leaves the value unchanged.
(Over `ℂ` this would instead conjugate, and the product would be *sesquilinear*
rather than bilinear; over `ℝ` conjugation does nothing.) This is what collapses
the two cross terms `⟪u, v⟫ + ⟪v, u⟫` into a single `2 • ⟪u, v⟫` once an
expansion is complete. -/

-- Symmetry of the real inner product.
example (x y : F) : ⟪x, y⟫_ℝ = ⟪y, x⟫_ℝ := real_inner_comm y x

/-! The other half of the toolkit — the bridge `⟪w, w⟫_ℝ = ‖w‖ ^ 2`
(`real_inner_self_eq_norm_sq`) that swaps between a self inner product and a
squared norm — is not bilinearity, so it lives with the proofs that use it
rather than here. -/

end Analysis.Bilinearity
