/-
# The parallelogram law

Take any parallelogram and look at its two diagonals. The parallelogram law
says that the sum of the squares of the diagonals equals the sum of the squares
of all four sides. If the two sides meeting at a corner are the vectors `u` and
`v`, then the diagonals are `u + v` and `u - v`, and the four side lengths are
`‖u‖, ‖v‖, ‖u‖, ‖v‖`. The identity reads:

    ‖u + v‖² + ‖u - v‖² = 2‖u‖² + 2‖v‖²

Like the Pythagorean theorem, this is a fact about *lengths* that becomes a
short calculation once we pass to *inner products*, where bilinearity does the
work. But the contrast with Pythagoras is the whole point of this file.

## A contrast with Pythagoras

Both proofs begin by expanding a squared norm via bilinearity, and both produce
the same cross term `⟪u, v⟫`. The difference is what becomes of that cross term.

In the Pythagorean theorem we *assume* `u` and `v` are orthogonal, so
`⟪u, v⟫ = 0`: the hypothesis reaches in and **kills** the cross term, leaving
`‖u + v‖² = ‖u‖² + ‖v‖²`. The orthogonality is exactly what the proof needs,
and without it the statement is simply false.

The parallelogram law asks for **no hypothesis at all** — it holds for every
pair of vectors. Here the cross terms are not killed; they **cancel**. Expand
the two diagonals separately and watch the cross term appear with opposite signs:

    ‖u + v‖² = ‖u‖² + 2⟪u, v⟫ + ‖v‖²
    ‖u - v‖² = ‖u‖² − 2⟪u, v⟫ + ‖v‖²

Each expansion keeps its cross term; neither is zero in general. But when we add
the two lines the `+2⟪u, v⟫` meets the `−2⟪u, v⟫` and they annihilate, leaving
`2‖u‖² + 2‖v‖²`. So where Pythagoras needs orthogonality to *remove* the cross
term from a single expansion, the parallelogram law lets *two* expansions remove
each other's cross terms for free.

## The setting

We work over an arbitrary type `F` carrying two pieces of structure:

  * `[SeminormedAddCommGroup F]` — vectors can be added, negated, and measured by
    a *seminorm* `‖·‖`: a length in every respect but one — it need not be
    *definite*, so a nonzero vector may still have `‖x‖ = 0`.
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied to
    the seminorm by `⟪x, x⟫_ℝ = ‖x‖²`.

A seminorm is the weakest structure the inner product itself requires —
`InnerProductSpace` is declared over a seminormed group — and the calculation
below never appeals to *definiteness* (`‖x‖ = 0 → x = 0`). Stating the law over a
seminorm rather than the stronger `NormedAddCommGroup` is the same
weakest-structure discipline `Analysis.Convergence` follows, and it is how
Mathlib files this result (in its `Norm_Seminormed` section). Nothing below
mentions a dimension or a coordinate either, so the same theorem covers the
plane, `ℝⁿ`, and infinite-dimensional spaces alike.

## The argument

Rewrite each squared norm as a self inner product and expand by bilinearity.
For the sum, additivity in both slots gives four pairings, two of them squared
norms and two of them the symmetric cross term:

    ‖u + v‖²
      = ⟪u + v, u + v⟫                 (norm-squared is the self inner product)
      = ‖u‖² + ⟪u, v⟫ + ⟪v, u⟫ + ‖v‖²  (bilinearity, then fold the self terms)

For the difference, subtractivity in both slots flips the sign on the cross
pairings:

    ‖u - v‖²
      = ⟪u - v, u - v⟫                 (norm-squared is the self inner product)
      = ‖u‖² − ⟪u, v⟫ − ⟪v, u⟫ + ‖v‖²  (bilinearity, then fold the self terms)

Add the two right-hand sides. The cross terms `⟪u, v⟫` and `⟪v, u⟫` appear once
with a `+` and once with a `−`, so every one of them cancels, leaving
`2‖u‖² + 2‖v‖²` — pure arithmetic that `ring` finishes off.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Geometry

/-! We fix an arbitrary real inner-product space `F` for the whole file. Stating
the constraints once with `variable` lets the theorem below inherit them
automatically; Lean inserts only the binders a declaration actually mentions. -/
variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Parallelogram law.** For *any* two vectors, the sum of the squared norms
of the sum and the difference equals twice the sum of the individual squared
norms. No orthogonality is required: the cross terms cancel on their own.

`calc` writes the proof as a chain of equalities: after each `_ =` comes the
next expression, and after `:=` comes the justification connecting it to the
previous one. Read top to bottom, the chain *is* the blackboard derivation. -/
theorem parallelogram_law (u v : F) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  calc ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2
      /- A norm and its inner product are two views of the same quantity:
         `⟪w, w⟫ = ‖w‖²`. We take the second view for both diagonals at once,
         recasting each squared length as a self inner product where bilinearity
         can do the work. That identity is `real_inner_self_eq_norm_sq`. -/
      = ⟪u + v, u + v⟫_ℝ + ⟪u - v, u - v⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      /- An inner product is linear in each argument, so we expand each one the
         way we would multiply out a product. `inner_add_left` distributes the
         sum across the first slot of the first term; `inner_sub_left`
         distributes the difference across the first slot of the second. -/
    _ = (⟪u, u + v⟫_ℝ + ⟪v, u + v⟫_ℝ)
          + (⟪u, u - v⟫_ℝ - ⟪v, u - v⟫_ℝ) := by
          rw [inner_add_left, inner_sub_left]
      /- Now expand the second slot of each pairing. `inner_add_right` splits the
         sum on the left diagonal and `inner_sub_right` splits the difference on
         the right diagonal, applied twice each to reach eight pairings in all.
         The signs from the difference flip exactly the cross pairings. -/
    _ = (⟪u, u⟫_ℝ + ⟪u, v⟫_ℝ) + (⟪v, u⟫_ℝ + ⟪v, v⟫_ℝ)
          + ((⟪u, u⟫_ℝ - ⟪u, v⟫_ℝ) - (⟪v, u⟫_ℝ - ⟪v, v⟫_ℝ)) := by
          rw [inner_add_right, inner_add_right, inner_sub_right, inner_sub_right]
      /- Four of those eight pairings are a vector with itself. Reading
         `real_inner_self_eq_norm_sq` in the other direction folds each `⟪u, u⟫`
         and `⟪v, v⟫` back into the squared norms that belong in the answer. -/
    _ = (‖u‖ ^ 2 + ⟪u, v⟫_ℝ) + (⟪v, u⟫_ℝ + ‖v‖ ^ 2)
          + ((‖u‖ ^ 2 - ⟪u, v⟫_ℝ) - (⟪v, u⟫_ℝ - ‖v‖ ^ 2)) := by
          rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v]
      /- What remains are the cross terms, each appearing once with a `+` and
         once with a `−`. They cancel in pairs, and clearing the leftover
         arithmetic into `2‖u‖² + 2‖v‖²` is exactly the job of `ring`. (No
         appeal to symmetry is needed: `⟪u, v⟫` cancels against `⟪u, v⟫` and
         `⟪v, u⟫` against `⟪v, u⟫`, term by term.) -/
    _ = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by ring

/-! ### The same theorem in Mathlib

Mathlib proves this as `parallelogram_law_with_norm`, over the same seminorm. It
takes the scalar field as an explicit first argument, `ℝ` for us, since the
identity holds over any `RCLike` field and the vectors alone do not pin it down.
It also gathers the right side as `2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)`, so recovering our
form is a single `ring` step after rewriting with it: -/

example (u v : F) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  rw [parallelogram_law_with_norm ℝ u v]; ring

/-! The companion `parallelogram_law` states the same identity with inner products
in place of norms, `⟪u + v, u + v⟫ + ⟪u - v, u - v⟫ = 2 * (⟪u, u⟫ + ⟪v, v⟫)`.
Rewriting each self-pairing `⟪x, x⟫_ℝ` back into `‖x‖ ^ 2` recovers our form: -/

example (u v : F) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := _root_.parallelogram_law (𝕜 := ℝ) (x := u) (y := v)
  simp only [real_inner_self_eq_norm_sq] at h
  linarith [h]

end Geometry
