import Surfaces.«1-SmoothSurfaces» /- AllowablePatch, e₁, e₂ -/
import Mathlib.Analysis.Calculus.ContDiff.Defs /- ContDiff -/
import Mathlib.Analysis.Calculus.Deriv.Basic /- deriv -/
import Mathlib.Analysis.Calculus.LineDeriv.Basic /- lineDeriv -/
import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, y⟫ -/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace /- MeasurableSpace ℝ² -/
import Mathlib.Analysis.Normed.Lp.WithLp /- WithLp.toLp -/
import Mathlib.Analysis.Real.Sqrt /- √ -/
import Mathlib.LinearAlgebra.CrossProduct /- crossProduct -/
import Mathlib.LinearAlgebra.Matrix.Defs /- Matrix, Matrix.transpose -/
import Mathlib.LinearAlgebra.Matrix.Notation /- !![a, b; c, d] -/
import Mathlib.LinearAlgebra.Span.Defs /- Submodule.span -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic /- ∫ x in R, f x -/
import Mathlib.MeasureTheory.MeasurableSpace.Defs /- MeasurableSet -/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis /- volume on ℝ² -/

/-!
# 2. The tangent plane and the first fundamental form

A *tangent vector* to `S` at `p` is the velocity at `p` of a curve in `S` (Pressley,
Definition 4.4.1). The tangent vectors form the *tangent plane* `T_p S`, and for any allowable
patch it is the plane spanned by `σ_u` and `σ_v` (Proposition 4.4.2).

The *first fundamental form* is the dot product restricted to tangent vectors (Definition 6.1.1).
On a patch it is recorded by the three functions `E = σ_u · σ_u`, `F = σ_u · σ_v`, and
`G = σ_v · σ_v`, which determine lengths, angles, and areas on the surface.
-/

open scoped ContDiff Topology RealInnerProductSpace

/-- `∂ᵤ f (q)`, the partial derivative of `f` with respect to `u`, as Mathlib's line derivative in
the direction `e₁` -/
noncomputable def partialU {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ² → X) (q : ℝ²) : X :=
  lineDeriv ℝ f q e₁

/-- `∂ᵥ f (q)`, the partial derivative of `f` with respect to `v` -/
noncomputable def partialV {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ² → X) (q : ℝ²) : X :=
  lineDeriv ℝ f q e₂

@[inherit_doc] prefix:max "∂ᵤ" => partialU
@[inherit_doc] prefix:max "∂ᵥ" => partialV

/-- `a × b`, the cross product. Mathlib's `crossProduct` acts on `Fin 3 → ℝ`, the underlying
coordinates of a point of `ℝ³`. -/
noncomputable def cross (a b : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (crossProduct a.ofLp b.ofLp)

/-- **Tangent vectors** (Pressley, Definition 4.4.1). The velocities `γ'(0)` of smooth curves `γ`
with `γ(0) = p` that lie in `S` near `t = 0`. -/
def tangentSpace (S : Set ℝ³) (p : ℝ³) : Set ℝ³ :=
  {w | ∃ γ : ℝ → ℝ³, ContDiff ℝ ∞ γ ∧ (∀ᶠ t in 𝓝 0, γ t ∈ S) ∧ γ 0 = p ∧ deriv γ 0 = w}

/-- **The tangent plane is spanned by `σ_u` and `σ_v`** (Pressley, Proposition 4.4.2), whichever
allowable patch is used. -/
theorem AllowablePatch.tangentSpace_eq {S : Set ℝ³} (σ : AllowablePatch S) {q : ℝ²}
    (hq : q ∈ σ.U) :
    tangentSpace S (σ.toFun q) = Submodule.span ℝ {∂ᵤ σ.toFun q, ∂ᵥ σ.toFun q} :=
  sorry

namespace Patch

variable (σ : ℝ² → ℝ³) (q : ℝ²)

/-- **The standard unit normal** `N = σ_u × σ_v / ‖σ_u × σ_v‖` (Pressley, Section 4.5) -/
noncomputable def normal : ℝ³ :=
  ‖cross (∂ᵤ σ q) (∂ᵥ σ q)‖⁻¹ • cross (∂ᵤ σ q) (∂ᵥ σ q)

/-- `E = σ_u · σ_u` (Pressley, Section 6.1) -/
noncomputable def E : ℝ := ⟪∂ᵤ σ q, ∂ᵤ σ q⟫

/-- `F = σ_u · σ_v` -/
noncomputable def F : ℝ := ⟪∂ᵤ σ q, ∂ᵥ σ q⟫

/-- `G = σ_v · σ_v` -/
noncomputable def G : ℝ := ⟪∂ᵥ σ q, ∂ᵥ σ q⟫

/-- The matrix `[[E, F], [F, G]]` of the first fundamental form -/
noncomputable def firstFundamentalMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E σ q, F σ q; F σ q, G σ q]

/-- **The area element** `‖σ_u × σ_v‖`. The area of `σ(R)` is `∫∫_R ‖σ_u × σ_v‖ du dv`. -/
noncomputable def areaElement : ℝ :=
  ‖cross (∂ᵤ σ q) (∂ᵥ σ q)‖

/-- **The area of `σ(R)`** (Pressley, Definition 6.4.1) -/
noncomputable def area (R : Set ℝ²) : ℝ :=
  ∫ x in R, areaElement σ x

end Patch

open Patch

/-- The Jacobian matrix of `Φ : ℝ² → ℝ²` at `q` -/
noncomputable def jacobian (Φ : ℝ² → ℝ²) (q : ℝ²) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![∂ᵤ Φ q 0, ∂ᵥ Φ q 0; ∂ᵤ Φ q 1, ∂ᵥ Φ q 1]

/-- **The first fundamental form under reparametrization** (Pressley, Section 6.1). If
`σ̃ = σ ∘ Φ`, then `F_I(σ̃) = Jᵀ F_I(σ) J`, where `J` is the Jacobian matrix of `Φ`. -/
theorem firstFundamentalMatrix_comp {σ : ℝ² → ℝ³} {Φ : ℝ² → ℝ²} {q : ℝ²}
    (hσ : DifferentiableAt ℝ σ (Φ q)) (hΦ : DifferentiableAt ℝ Φ q) :
    firstFundamentalMatrix (σ ∘ Φ) q =
      (jacobian Φ q).transpose * firstFundamentalMatrix σ (Φ q) * jacobian Φ q :=
  sorry

/-- `‖σ_u × σ_v‖ = √(EG - F²)` (Pressley, Proposition 6.4.2) -/
theorem areaElement_eq (σ : ℝ² → ℝ³) (q : ℝ²) :
    areaElement σ q = √(E σ q * G σ q - F σ q ^ 2) :=
  sorry

/-- **Area does not depend on the patch** (Pressley, Proposition 6.4.3). If `Φ` is smooth and
one-to-one on an open `Ũ`, the area of `(σ ∘ Φ)(R)` equals the area of `σ(Φ(R))`. -/
theorem area_comp {σ : ℝ² → ℝ³} {Φ : ℝ² → ℝ²} {Ũ R : Set ℝ²}
    (hŨ : IsOpen Ũ) (hΦ : ContDiffOn ℝ ∞ Φ Ũ) (Φ_inj : Set.InjOn Φ Ũ)
    (hσ : ContDiffOn ℝ ∞ σ (Φ '' Ũ)) (hR : MeasurableSet R) (R_sub : R ⊆ Ũ) :
    area (σ ∘ Φ) R = area σ (Φ '' R) :=
  sorry
