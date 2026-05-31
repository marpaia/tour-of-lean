/-
# The Pythagorean theorem

One can prove the Pythagorean theorem in any number of ways — rearranging the
areas of squares, chasing similar triangles, or invoking trigonometry. The
approach taken here is algebraic, and it is the one that generalizes furthest:
it works through *inner products*, turning a statement about lengths into a
short calculation that bilinearity carries almost on its own.

An *inner product space* is a vector space equipped with an inner product
`⟪·,·⟫` — an operation that multiplies two vectors into a scalar, generalizing
the dot product and, with it, the very notions of length and angle. A Euclidean
space is just one such space (`ℝⁿ` under the standard dot product); phrasing
Pythagoras over an abstract inner product space instead asks for exactly the
structure the proof uses and nothing more, so the theorem lands in every finite
dimension and even in infinite-dimensional spaces at once.

In a real inner-product space, two vectors `u` and `v` are *orthogonal* when
their inner product `⟪u, v⟫_ℝ` is zero. When that happens, the squared length
of their sum splits cleanly into the sum of their squared lengths:

    ‖u + v‖² = ‖u‖² + ‖v‖²

This is the `a² + b² = c²` of right triangles, written in the language that
makes it true in every dimension at once.

## The setting

We work over an arbitrary type `F` carrying two pieces of structure:

  * `[SeminormedAddCommGroup F]` — vectors can be added, negated, and measured by
    a *seminorm* `‖·‖`: a length in every respect but one — it need not be
    *definite*, so a nonzero vector may still have `‖x‖ = 0`.
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied to
    the seminorm by `⟪x, x⟫_ℝ = ‖x‖²`.

A seminorm is the weakest structure the inner product itself requires —
`InnerProductSpace` is declared over a seminormed group — and the calculation
below never appeals to *definiteness* (`‖x‖ = 0 → x = 0`). Stating the theorem
over a seminorm rather than the stronger `NormedAddCommGroup` is the same
weakest-structure discipline `Analysis.Convergence` follows, and it is how
Mathlib files this result (in its `Norm_Seminormed` section). Nothing below
mentions a dimension or a coordinate either, so the same theorem covers the
plane, `ℝⁿ`, and infinite-dimensional spaces alike.

## The argument

Rewrite the squared norm as an inner product, then expand by bilinearity:

    ‖u + v‖²
      = ⟪u + v, u + v⟫                 (norm-squared is the self inner product)
      = ⟪u, u + v⟫ + ⟪v, u + v⟫        (additivity in the first argument)
      = ⟪u,u⟫ + ⟪u,v⟫ + ⟪v,u⟫ + ⟪v,v⟫  (additivity in the second argument)
      = ‖u‖² + ⟪u,v⟫ + ⟪v,u⟫ + ‖v‖²    (self inner product is norm-squared)
      = ‖u‖² + 0 + 0 + ‖v‖²            (orthogonality, with ⟪v,u⟫ = ⟪u,v⟫)
      = ‖u‖² + ‖v‖²                    (arithmetic)

The cross terms `⟪u,v⟫` and `⟪v,u⟫` are precisely what orthogonality sends to
zero — they are the whole reason the hypothesis is needed.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Geometry

/-! We fix an arbitrary real inner-product space `F` for the whole file. Stating
the constraints once with `variable` lets the theorem below inherit them
automatically; Lean inserts only the binders a declaration actually mentions. -/
variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Pythagorean theorem.** If `u` and `v` are orthogonal, the squared norm of
their sum is the sum of their squared norms.

`calc` writes the proof as a chain of equalities: after each `_ =` comes the
next expression, and after `:=` comes the justification connecting it to the
previous one. Read top to bottom, the chain *is* the blackboard derivation. -/
theorem pythagorean_theorem (u v : F) (h : ⟪u, v⟫_ℝ = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  calc ‖u + v‖ ^ 2
      /- A norm and its inner product are two views of the same quantity:
         `⟪w, w⟫ = ‖w‖²`. We start by taking the second view, recasting the
         squared length of `u + v` as an inner product where bilinearity can do
         the work. That identity is `real_inner_self_eq_norm_sq`. -/
      = ⟪u + v, u + v⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq]
      /- An inner product is linear in each argument, so we expand it the way we
         would multiply out `(u + v)·(u + v)`. First the left-hand factor:
         `inner_add_left` distributes the sum across the first slot. -/
    _ = ⟪u, u + v⟫_ℝ + ⟪v, u + v⟫_ℝ := by
          rw [inner_add_left]
      /- Then the right-hand factor of each term, via `inner_add_right`. We
         apply it twice — once per inner product — to reach the fully expanded
         sum of four pairings. -/
    _ = ⟪u, u⟫_ℝ + ⟪u, v⟫_ℝ + (⟪v, u⟫_ℝ + ⟪v, v⟫_ℝ) := by
          rw [inner_add_right, inner_add_right]
      /- Two of those four pairings are a vector with itself. Reading
         `real_inner_self_eq_norm_sq` in the other direction folds `⟪u, u⟫` and
         `⟪v, v⟫` back into the squared norms that belong in the final answer. -/
    _ = ‖u‖ ^ 2 + ⟪u, v⟫_ℝ + (⟪v, u⟫_ℝ + ‖v‖ ^ 2) := by
          rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v]
      /- What is left are the two cross terms — and this is the one place the
         hypothesis earns its keep. Orthogonality `h` sends `⟪u, v⟫` to zero
         directly; because the real inner product is symmetric
         (`real_inner_comm`), `⟪v, u⟫` is the same number, so it vanishes too. -/
    _ = ‖u‖ ^ 2 + 0 + (0 + ‖v‖ ^ 2) := by
          rw [h, real_inner_comm u v, h]
      /- With both cross terms gone, only the zeros remain to be cleared away,
         which is pure arithmetic and the job of `ring`. -/
    _ = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by ring

end Geometry
