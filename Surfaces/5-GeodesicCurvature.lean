import Surfaces.«4-GaussianCurvature» /- SurfacePatch -/
import Surfaces.Notation /- ℝ², ℝ³, cross -/
import Surfaces.«1-TangentPlane» /- tangentPlane -/
import Surfaces.«2-Orientation» /- normal -/
import Mathlib.Analysis.Calculus.ContDiff.Defs /- ContDiff, ContDiffOn -/
import Mathlib.Analysis.Calculus.Deriv.Basic /- deriv -/
import Mathlib.Analysis.Complex.Trigonometric /- Real.cos, Real.sin -/
import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, y⟫ -/
import Mathlib.Analysis.InnerProductSpace.Orthonormal /- Orthonormal -/
import Mathlib.Order.Interval.Set.Defs /- Set.Icc -/

/-!
# 5. Geodesic curvature

A smooth curve `c` in the parameter set `U` traces the curve `γ = σ ∘ c` on the surface. If `γ` is
unit-speed, then `γ̇`, `N`, and `N × γ̇` are perpendicular unit vectors, and the acceleration splits
as

  `γ̈ = κn N + κg (N × γ̇)`

(Pressley, Equation 7.7). The *geodesic curvature* `κg` is the part of the curving that is seen
from within the surface.

To measure how `γ̇` turns, compare it with an *orthonormal frame*, two perpendicular unit vectors
`e′` and `e″` in each tangent plane. If `θ` is the angle from `e′` to `γ̇`, then
`θ̇ = κg + e′ · ė″` (Equation 13.4). The tangent turns by `κg` relative to the surface, and the
frame itself turns by `e′ · ė″`.
-/

open scoped ContDiff RealInnerProductSpace

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S)

/-- **Geodesic curvature** `κg = γ̈ · (N × γ̇)` of `γ = σ ∘ c` (Pressley, Proposition 7.3.2) -/
noncomputable def geodesicCurvature (c : ℝ → ℝ²) (s : ℝ) : ℝ :=
  let γ := σ ∘ c
  ⟪deriv (deriv γ) s, cross (σ.normal (c s)) (deriv γ s)⟫

/-- **Orthonormal frames** (Pressley, Section 13.1). At each point of the patch, an orthonormal
basis `e′, e″` of the tangent plane, varying smoothly and oriented so that `e′ × e″ = N`. -/
structure OrthonormalFrame where
  /-- `e′` -/
  e' : ℝ² → ℝ³
  /-- `e″` -/
  e'' : ℝ² → ℝ³
  /-- `e′` is smooth -/
  smooth_e' : ContDiffOn ℝ ∞ e' σ.U
  /-- `e″` is smooth -/
  smooth_e'' : ContDiffOn ℝ ∞ e'' σ.U
  /-- `e′` and `e″` lie in the tangent plane -/
  mem_tangentPlane : ∀ q ∈ σ.U, e' q ∈ σ.tangentPlane q ∧ e'' q ∈ σ.tangentPlane q
  /-- `e′` and `e″` are perpendicular unit vectors -/
  orthonormal : ∀ q ∈ σ.U, Orthonormal ℝ ![e' q, e'' q]
  /-- `e′ × e″ = N`, so that turning from `e′` to `e″` is anticlockwise about the normal -/
  cross_eq_normal : ∀ q ∈ σ.U, cross (e' q) (e'' q) = σ.normal q

/-- **Every patch has an orthonormal frame.** Gram–Schmidt applied to `σᵤ` and `σᵥ`
gives one. -/
theorem nonempty_orthonormalFrame : Nonempty σ.OrthonormalFrame :=
  sorry

variable {σ}

/-- **The tangent angle** (Pressley, Equation 13.4). Along a unit-speed curve `γ = σ ∘ c`, there is
a smooth angle `θ` with `γ̇ = cos θ e′ + sin θ e″`, the oriented angle from `e′` to `γ̇` up to a
multiple of `2π`, and it turns at the rate `θ̇ = κg + e′ · ė″`. -/
theorem OrthonormalFrame.exists_tangentAngle (frame : σ.OrthonormalFrame) {c : ℝ → ℝ²} {ℓ : ℝ}
    (smooth : ContDiff ℝ ∞ c) (in_U : ∀ s ∈ Set.Icc 0 ℓ, c s ∈ σ.U)
    (unit_speed : ∀ s ∈ Set.Icc 0 ℓ, ‖deriv (σ ∘ c) s‖ = 1) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ ∀ s ∈ Set.Icc 0 ℓ,
      deriv (σ ∘ c) s = Real.cos (θ s) • frame.e' (c s) + Real.sin (θ s) • frame.e'' (c s) ∧
        deriv θ s = σ.geodesicCurvature c s + ⟪frame.e' (c s), deriv (frame.e'' ∘ c) s⟫ :=
  sorry

end SurfacePatch
