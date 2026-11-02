module

public import Surfaces.«3-AreaElement» /- E, F, G -/
public import Surfaces.«2-Orientation» /- normal -/
public import Surfaces.Notation /- σᵤ, σᵥ, σᵤᵤ, σᵤᵥ, σᵥᵥ, ∂ᵤ, ∂ᵥ -/
public import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, y⟫ -/

/-!
# 4. Gaussian curvature

The *second fundamental form* measures how the surface bends away from its tangent plane. On a
patch it is recorded by

  `L = σᵤᵤ · N`,  `M = σᵤᵥ · N`,  `N = σᵥᵥ · N`

(Pressley, Section 7.1). Pressley defines the *Gaussian curvature* `K` as the determinant of the
Weingarten map, the derivative of `-N` (Definition 8.1.1), and computes it in terms of the two
fundamental forms (Corollary 8.1.3). We take that formula as the definition,

  `K = (LN - M²) / (EG - F²)`,

the determinant of the second fundamental form divided by the determinant of the first.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S) (q : ℝ²)

/-- `L = σᵤᵤ · N` -/
noncomputable def L : ℝ := ⟪σᵤᵤ q, σ.normal q⟫

/-- `M = σᵤᵥ · N` -/
noncomputable def M : ℝ := ⟪σᵤᵥ q, σ.normal q⟫

/-- `N = σᵥᵥ · N` -/
noncomputable def N : ℝ := ⟪σᵥᵥ q, σ.normal q⟫

/-- **Gaussian curvature** `K = (LN - M²) / (EG - F²)` (Pressley, Corollary 8.1.3) -/
noncomputable def K : ℝ :=
  (σ.L q * σ.N q - σ.M q ^ 2) / (σ.E q * σ.G q - σ.F q ^ 2)

variable {q}

/-- **How the normal turns** (Pressley, Lemma 7.2.3). `Nᵤ · σᵤ = -L`, `Nᵤ · σᵥ = -M`,
`Nᵥ · σᵤ = -M`, and `Nᵥ · σᵥ = -N`. -/
theorem inner_partial_normal (q_in_U : q ∈ σ.U) :
    ⟪∂ᵤ σ.normal q, σᵤ q⟫ = -σ.L q ∧
      ⟪∂ᵤ σ.normal q, σᵥ q⟫ = -σ.M q ∧
      ⟪∂ᵥ σ.normal q, σᵤ q⟫ = -σ.M q ∧
      ⟪∂ᵥ σ.normal q, σᵥ q⟫ = -σ.N q :=
  sorry

end SurfacePatch
