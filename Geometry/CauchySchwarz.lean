import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.QuadraticDiscriminant

open scoped InnerProductSpace

namespace Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Cauchy–Schwarz inequality.** `|⟪u, v⟫| ≤ ‖u‖ ‖v‖`, by the discriminant argument. -/
theorem cauchy_schwarz (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  -- `⟪u, v⟫² ≤ ‖u‖² ‖v‖²`, from the two steps below.
  have inner_sq_le : ⟪u, v⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    -- For every real `t`, `0 ≤ ‖u - t v‖² = ‖v‖² t² - 2⟪u, v⟫ t + ‖u‖²`.
    -- `t²` is written `t * t` because that is the form `discrim_le_zero` expects.
    have quadratic_nonneg : ∀ t : ℝ,
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
    -- A quadratic that is never negative has discriminant `≤ 0`,
    -- so `4⟪u, v⟫² - 4‖v‖² ‖u‖² ≤ 0`.
    have discriminant_nonpos := discrim_le_zero quadratic_nonneg
    rw [discrim] at discriminant_nonpos
    linarith
  -- Take square roots, since `0 ≤ ‖u‖ ‖v‖`.
  rw [← mul_pow] at inner_sq_le
  exact abs_le_of_sq_le_sq inner_sq_le (by positivity)

/-- The same inequality, from Mathlib. -/
example (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v

end Geometry
