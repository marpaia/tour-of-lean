import Surfaces.«2-TangentPlane» /- ∂ᵤ, ∂ᵥ, normal, E, F, G, firstFundamentalMatrix -/
import Mathlib.Analysis.Complex.Trigonometric /- Real.cos, Real.sin -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- Real.pi -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic /- Matrix.det -/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse /- A⁻¹ -/
import Mathlib.LinearAlgebra.Matrix.Notation /- !![a, b; c, d] -/

/-!
# 3. Curvature

The *second fundamental form* measures how the surface bends away from its tangent plane. On a
patch it is recorded by `L = σ_uu · N`, `M = σ_uv · N`, and `N = σ_vv · N` (Pressley, Section 7.1).
The *Weingarten map* `W` is minus the derivative of the unit normal, and its matrix in the basis
`σ_u, σ_v` is `F_I⁻¹ F_II` (Proposition 8.1.2). The *Gaussian curvature* is its determinant
(Definition 8.1.1),

  `K = det W = (LN - M²) / (EG - F²)`.

Changing the patch or the direction of the normal does not change `K`, so `K` is a function on the
surface itself.
-/

open scoped ContDiff RealInnerProductSpace

open Patch

namespace Patch

variable (σ : ℝ² → ℝ³) (q : ℝ²)

/-- `L = σ_uu · N` (Pressley, Section 7.1) -/
noncomputable def L : ℝ := ⟪∂ᵤ (∂ᵤ σ) q, normal σ q⟫

/-- `M = σ_uv · N` -/
noncomputable def M : ℝ := ⟪∂ᵥ (∂ᵤ σ) q, normal σ q⟫

/-- `N = σ_vv · N` -/
noncomputable def N : ℝ := ⟪∂ᵥ (∂ᵥ σ) q, normal σ q⟫

/-- The matrix `[[L, M], [M, N]]` of the second fundamental form -/
noncomputable def secondFundamentalMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![L σ q, M σ q; M σ q, N σ q]

/-- **Gaussian curvature** (Pressley, Definition 8.1.1 and Proposition 8.1.2). The determinant of
the Weingarten map, whose matrix is `F_I⁻¹ F_II`. -/
noncomputable def K : ℝ :=
  (firstFundamentalMatrix σ q)⁻¹ * secondFundamentalMatrix σ q |>.det

end Patch

/-- **The derivatives of the normal** (Pressley, Lemma 7.2.3). `N_u · σ_u = -L`,
`N_u · σ_v = N_v · σ_u = -M`, and `N_v · σ_v = -N`. -/
theorem partial_normal_inner {S : Set ℝ³} (σ : AllowablePatch S) {q : ℝ²} (hq : q ∈ σ.U) :
    ⟪∂ᵤ (normal σ.toFun) q, ∂ᵤ σ.toFun q⟫ = -L σ.toFun q ∧
      ⟪∂ᵤ (normal σ.toFun) q, ∂ᵥ σ.toFun q⟫ = -M σ.toFun q ∧
      ⟪∂ᵥ (normal σ.toFun) q, ∂ᵤ σ.toFun q⟫ = -M σ.toFun q ∧
      ⟪∂ᵥ (normal σ.toFun) q, ∂ᵥ σ.toFun q⟫ = -N σ.toFun q :=
  sorry

/-- `K = (LN - M²) / (EG - F²)` (Pressley, Corollary 8.1.3) -/
theorem K_eq {S : Set ℝ³} (σ : AllowablePatch S) {q : ℝ²} (hq : q ∈ σ.U) :
    K σ.toFun q =
      (L σ.toFun q * N σ.toFun q - M σ.toFun q ^ 2) /
        (E σ.toFun q * G σ.toFun q - F σ.toFun q ^ 2) :=
  sorry

/-- **`K` is a function on the surface** (Pressley, Section 8.1). Two allowable patches give the
same Gaussian curvature at the same point of `S`. -/
theorem K_eq_of_eq {S : Set ℝ³} (σ τ : AllowablePatch S) {q q' : ℝ²}
    (hq : q ∈ σ.U) (hq' : q' ∈ τ.U) (same_point : σ.toFun q = τ.toFun q') :
    K σ.toFun q = K τ.toFun q' :=
  sorry

/-- The sphere of radius `r` in latitude `θ` and longitude `φ` (Pressley, Example 4.1.4) -/
noncomputable def spherePatch (r : ℝ) (x : ℝ²) : ℝ³ :=
  let θ := x 0
  let φ := x 1
  !₂[r * Real.cos θ * Real.cos φ, r * Real.cos θ * Real.sin φ, r * Real.sin θ]

/-- The circular cylinder of radius `1` about the `z`-axis -/
noncomputable def cylinderPatch (x : ℝ²) : ℝ³ :=
  let u := x 0
  let v := x 1
  !₂[Real.cos u, Real.sin u, v]

/-- **The sphere has constant curvature `1 / r²`** (Pressley, Section 8.1) -/
theorem K_spherePatch {r : ℝ} (hr : 0 < r) {x : ℝ²} (hx : |x 0| < Real.pi / 2) :
    K (spherePatch r) x = 1 / r ^ 2 :=
  sorry

/-- **The cylinder is flat.** It bends in one direction only, and `K = 0`. -/
theorem K_cylinderPatch (x : ℝ²) : K cylinderPatch x = 0 :=
  sorry
