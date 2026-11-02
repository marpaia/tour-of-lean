import Surfaces.«0-Definition» /- SurfacePatch, AllowablePatch, IsSmoothSurface -/
import Mathlib.Analysis.Calculus.ContDiff.Defs /- ContDiffOn -/
import Mathlib.Analysis.Calculus.FDeriv.Defs /- fderiv -/
import Mathlib.Data.Set.Function /- Function.invFunOn -/
import Mathlib.Data.Set.Operations /- Set.BijOn, Set.InvOn -/
import Mathlib.Order.Filter.Defs /- ∀ᶠ -/
import Mathlib.Topology.Defs.Filter /- 𝓝 -/
import Mathlib.Topology.MetricSpace.Pseudo.Defs /- Metric.sphere -/

/-!
# 1. Smooth surfaces

A point of a smooth surface usually lies in the windows of many patches. Any two of them are
related by a *transition map* `τ⁻¹ ∘ σ` between their parameter sets. The transition maps of a
smooth surface are smooth (Pressley, Proposition 4.2.6), so anything defined from one patch by
calculus can be compared with the same thing defined from another. The proof rests on the inverse
function theorem (Pressley, Theorem 5.6.1), which Mathlib has as
`ContDiffAt.toOpenPartialHomeomorph`.

The file ends with the two ways surfaces usually arise in practice: as level sets `f = 0` of a
function with nonzero derivative, and, in particular, as the sphere.
-/

open scoped ContDiff Topology

variable {S : Set ℝ³}

/-- **Transition maps.** `τ⁻¹ ∘ σ`, which sends a parameter of `σ` to the parameter of `τ` for the
same point of `S`. It is meaningful on the parameters of `σ` whose points lie in the window of
`τ`. -/
noncomputable def transitionMap (σ τ : SurfacePatch S) : ℝ² → ℝ² :=
  Function.invFunOn τ.toFun τ.U ∘ σ.toFun

/-- The parameters of `σ` whose points lie in the window of `τ` -/
def transitionDomain (σ τ : SurfacePatch S) : Set ℝ² :=
  σ.U ∩ σ.toFun ⁻¹' τ.W

/-- The domain of a transition map is open. -/
theorem isOpen_transitionDomain (σ τ : SurfacePatch S) : IsOpen (transitionDomain σ τ) :=
  sorry

/-- **Transition maps are smooth** (Pressley, Proposition 4.2.6). -/
theorem contDiffOn_transitionMap (σ τ : AllowablePatch S) :
    ContDiffOn ℝ ∞ (transitionMap σ.toSurfacePatch τ.toSurfacePatch)
      (transitionDomain σ.toSurfacePatch τ.toSurfacePatch) :=
  sorry

/-- **Reparametrization** (Pressley, Proposition 4.2.7). If `σ` is smooth and regular on `U`, and
`Φ : Ũ → U` is a bijection, smooth with smooth inverse, then `σ ∘ Φ` is smooth and regular on
`Ũ`. -/
theorem reparametrization
    {σ : ℝ² → ℝ³} {Φ Ψ : ℝ² → ℝ²} {U Ũ : Set ℝ²}
    (hσ : ContDiffOn ℝ ∞ σ U)
    (σ_regular : ∀ q ∈ U, Function.Injective (fderiv ℝ σ q))
    (hU : IsOpen U) (hŨ : IsOpen Ũ)
    (Φ_bij : Set.BijOn Φ Ũ U) (Φ_inv : Set.InvOn Ψ Φ Ũ U)
    (hΦ : ContDiffOn ℝ ∞ Φ Ũ) (hΨ : ContDiffOn ℝ ∞ Ψ U) :
    ContDiffOn ℝ ∞ (σ ∘ Φ) Ũ ∧ ∀ q ∈ Ũ, Function.Injective (fderiv ℝ (σ ∘ Φ) q) :=
  sorry

/-- **A smooth local inverse** (Pressley, Section 5.6). Near each point of its window, an allowable
patch has an inverse that extends to a smooth map on an open set of `ℝ³`. -/
theorem AllowablePatch.exists_smooth_inverse (σ : AllowablePatch S) {q : ℝ²} (hq : q ∈ σ.U) :
    ∃ W' : Set ℝ³, IsOpen W' ∧ σ.toFun q ∈ W' ∧
      ∃ F : ℝ³ → ℝ², ContDiffOn ℝ ∞ F W' ∧ ∀ᶠ x in 𝓝 q, F (σ.toFun x) = x :=
  sorry

/-- **Level sets** (Pressley, Theorem 5.1.1). If, near each of its points, `S` is the zero set of a
smooth function whose derivative does not vanish on `S`, then `S` is a smooth surface. -/
theorem isSmoothSurface_of_levelSet
    (h : ∀ p ∈ S, ∃ W : Set ℝ³, IsOpen W ∧ p ∈ W ∧ ∃ f : ℝ³ → ℝ, ContDiffOn ℝ ∞ f W ∧
      S ∩ W = {x ∈ W | f x = 0} ∧ ∀ x ∈ S ∩ W, fderiv ℝ f x ≠ 0) :
    IsSmoothSurface S :=
  sorry

/-- **The sphere is a smooth surface** (Pressley, Examples 4.1.4 and 4.2.5). It is the level set
`x² + y² + z² - r² = 0`, and no single patch covers it. -/
theorem isSmoothSurface_sphere {r : ℝ} (hr : 0 < r) :
    IsSmoothSurface (Metric.sphere (0 : ℝ³) r) :=
  sorry
