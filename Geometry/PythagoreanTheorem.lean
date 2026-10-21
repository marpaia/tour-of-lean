import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `‖u + v‖² = ‖u‖² + 2⟪u, v⟫ + ‖v‖²`

* `F` is any real inner product space, supplied by the `variable` line.
* `ring` does the commutative-ring bookkeeping that `Naturals` and `Integers` did by hand. -/
theorem norm_add_sq (u v : F) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
  calc ‖u + v‖ ^ 2
      = ⟪u + v, u + v⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq]
    _ = ⟪u, u⟫_ℝ + ⟪u, v⟫_ℝ + (⟪v, u⟫_ℝ + ⟪v, v⟫_ℝ) := by
          rw [
            inner_add_left,
            inner_add_right,
            inner_add_right
          ]
    _ = ‖u‖ ^ 2 + ⟪u, v⟫_ℝ + (⟪u, v⟫_ℝ + ‖v‖ ^ 2) := by
          rw [
            real_inner_self_eq_norm_sq u,
            real_inner_self_eq_norm_sq v,
            real_inner_comm u v
          ]
    _ = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by ring

/-- **Pythagorean theorem.** If `⟪u, v⟫ = 0` then `‖u + v‖² = ‖u‖² + ‖v‖²` -/
theorem pythagorean_theorem (u v : F) (h : ⟪u, v⟫_ℝ = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [
    norm_add_sq,
    h
  ]
  ring

/-- `⟪u, v⟫ = 0 ↔ ‖u + v‖² = ‖u‖² + ‖v‖²`

For the converse, `linarith` treats `⟪u, v⟫` as an unknown `x` and solves `2x = 0`. -/
theorem inner_eq_zero_iff_norm_add_sq (u v : F) :
    ⟪u, v⟫_ℝ = 0 ↔ ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  constructor
  · intro h
    exact pythagorean_theorem u v h
  · intro h
    rw [norm_add_sq] at h
    linarith

/-- The same equivalence, from Mathlib. -/
example (u v : F) :
    ⟪u, v⟫_ℝ = 0 ↔ ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [
    pow_two,
    pow_two,
    pow_two
  ]
  exact (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero u v).symm

end Geometry
