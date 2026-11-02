import Surfaces.«4-TheoremaEgregium» /- normal, cross, ∂ᵤ, ∂ᵥ -/
import Mathlib.Analysis.Calculus.ContDiff.Defs /- ContDiff -/
import Mathlib.Analysis.Calculus.Deriv.Basic /- deriv -/
import Mathlib.Analysis.Complex.Trigonometric /- Real.cos, Real.sin -/
import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, y⟫ -/

/-!
# 5. Curves on a surface

A curve in a patch is `γ = σ ∘ π`, where `π` is a curve in the parameter set. If `γ` is unit-speed,
then `γ̇`, `N`, and `N × γ̇` are perpendicular unit vectors, and `γ̈` is perpendicular to `γ̇`, so

  `γ̈ = κn N + κg N × γ̇`

(Pressley, Equation 7.7). The *normal curvature* `κn` is the part of the curving forced by the
surface, and the *geodesic curvature* `κg` is the part seen from within the surface. A *geodesic*
is a curve whose acceleration is perpendicular to the surface (Definition 9.1.1), so that it does
not curve within the surface at all.

Gauss–Bonnet measures `κg` against a smooth orthonormal frame `e′, e″` of the tangent planes. If
`θ` is the angle from `e′` to `γ̇`, then `κg = θ̇ - e′ · ė″` (Pressley, Equation 13.4).
-/

open scoped ContDiff RealInnerProductSpace

open Patch

namespace Patch

variable (σ : ℝ² → ℝ³) (π : ℝ → ℝ²) (t : ℝ)

/-- **Normal curvature** `κn = γ̈ · N` of `γ = σ ∘ π` (Pressley, Proposition 7.3.2) -/
noncomputable def normalCurvature : ℝ :=
  ⟪deriv (deriv (σ ∘ π)) t, normal σ (π t)⟫

/-- **Geodesic curvature** `κg = γ̈ · (N × γ̇)` of `γ = σ ∘ π` (Pressley, Proposition 7.3.2) -/
noncomputable def geodesicCurvature : ℝ :=
  ⟪deriv (deriv (σ ∘ π)) t, cross (normal σ (π t)) (deriv (σ ∘ π) t)⟫

end Patch

/-- **Geodesics** (Pressley, Definition 9.1.1). `γ̈` is perpendicular to the tangent plane, so it
is perpendicular to `σ_u` and `σ_v`. -/
def IsGeodesic (σ : ℝ² → ℝ³) (π : ℝ → ℝ²) : Prop :=
  ∀ t, ⟪deriv (deriv (σ ∘ π)) t, ∂ᵤ σ (π t)⟫ = 0 ∧ ⟪deriv (deriv (σ ∘ π)) t, ∂ᵥ σ (π t)⟫ = 0

variable {S : Set ℝ³} (σ : AllowablePatch S) {π : ℝ → ℝ²}

/-- **`κ² = κn² + κg²`** (Pressley, Proposition 7.3.2). For a unit-speed curve, the curvature
`κ = ‖γ̈‖` splits into its normal and geodesic parts. -/
theorem norm_sq_eq_normalCurvature_sq_add_geodesicCurvature_sq
    (hπ : ContDiff ℝ ∞ π) (in_U : ∀ t, π t ∈ σ.U)
    (unit_speed : ∀ t, ‖deriv (σ.toFun ∘ π) t‖ = 1) (t : ℝ) :
    ‖deriv (deriv (σ.toFun ∘ π)) t‖ ^ 2 =
      normalCurvature σ.toFun π t ^ 2 + geodesicCurvature σ.toFun π t ^ 2 :=
  sorry

/-- **Geodesics have constant speed** (Pressley, Proposition 9.1.2). -/
theorem IsGeodesic.norm_deriv_eq (hπ : ContDiff ℝ ∞ π) (in_U : ∀ t, π t ∈ σ.U)
    (geodesic : IsGeodesic σ.toFun π) (s t : ℝ) :
    ‖deriv (σ.toFun ∘ π) s‖ = ‖deriv (σ.toFun ∘ π) t‖ :=
  sorry

/-- **Geodesics are the curves with `κg = 0`** (Pressley, Proposition 9.1.3), among unit-speed
curves. -/
theorem isGeodesic_iff_geodesicCurvature_eq_zero (hπ : ContDiff ℝ ∞ π) (in_U : ∀ t, π t ∈ σ.U)
    (unit_speed : ∀ t, ‖deriv (σ.toFun ∘ π) t‖ = 1) :
    IsGeodesic σ.toFun π ↔ ∀ t, geodesicCurvature σ.toFun π t = 0 :=
  sorry

/-- **An orthonormal frame** (Pressley, Section 13.1). Smooth unit vectors `e′` and `e″` tangent to
the surface, perpendicular to each other, with `N = e′ × e″`. Gram–Schmidt applied to `σ_u` and
`σ_v` gives one. -/
theorem exists_orthonormal_frame :
    ∃ e' e'' : ℝ² → ℝ³, ContDiffOn ℝ ∞ e' σ.U ∧ ContDiffOn ℝ ∞ e'' σ.U ∧
      ∀ q ∈ σ.U, ‖e' q‖ = 1 ∧ ‖e'' q‖ = 1 ∧ ⟪e' q, e'' q⟫ = 0 ∧
        normal σ.toFun q = cross (e' q) (e'' q) :=
  sorry

/-- **`κg = θ̇ - e′ · ė″`** (Pressley, Equation 13.4). A unit-speed curve has a smooth angle `θ`
from `e′` to `γ̇`, so `γ̇ = cos θ e′ + sin θ e″`, and its geodesic curvature is the rate at which
`θ` turns, corrected by the turning of the frame. -/
theorem exists_angle {e' e'' : ℝ² → ℝ³} (he' : ContDiffOn ℝ ∞ e' σ.U)
    (he'' : ContDiffOn ℝ ∞ e'' σ.U)
    (frame : ∀ q ∈ σ.U, ‖e' q‖ = 1 ∧ ‖e'' q‖ = 1 ∧ ⟪e' q, e'' q⟫ = 0 ∧
      normal σ.toFun q = cross (e' q) (e'' q))
    (hπ : ContDiff ℝ ∞ π) (in_U : ∀ t, π t ∈ σ.U)
    (unit_speed : ∀ t, ‖deriv (σ.toFun ∘ π) t‖ = 1) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ ∀ t,
      deriv (σ.toFun ∘ π) t = Real.cos (θ t) • e' (π t) + Real.sin (θ t) • e'' (π t) ∧
        geodesicCurvature σ.toFun π t = deriv θ t - ⟪e' (π t), deriv (e'' ∘ π) t⟫ :=
  sorry
