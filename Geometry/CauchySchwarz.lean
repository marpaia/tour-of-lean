import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.QuadraticDiscriminant

open scoped InnerProductSpace

namespace Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem cauchy_schwarz (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  have key : ⟪u, v⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have hquad : ∀ t : ℝ,
        0 ≤ ‖v‖ ^ 2 * (t * t) + (-(2 * ⟪u, v⟫_ℝ)) * t + ‖u‖ ^ 2 := by
      intro t
      have h : 0 ≤ ⟪u - t • v, u - t • v⟫_ℝ := real_inner_self_nonneg
      rw [
        inner_sub_left,
        inner_sub_right,
        inner_sub_right,
        real_inner_smul_left,
        real_inner_smul_right,
        real_inner_smul_right,
        real_inner_smul_left,
        real_inner_self_eq_norm_sq u,
        real_inner_self_eq_norm_sq v,
        real_inner_comm u v
      ] at h
      linarith
    have hdisc := discrim_le_zero hquad
    rw [discrim] at hdisc
    linarith
  rw [← mul_pow] at key
  exact abs_le_of_sq_le_sq key (by positivity)

example (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v

end Geometry
