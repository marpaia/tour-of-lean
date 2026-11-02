module

public import Surfaces.«2-Orientation» /- SurfacePatch, tangentPlane, normal -/
public import Surfaces.Notation /- σᵤ, σᵥ, cross -/
public import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, y⟫ -/
public import Mathlib.Analysis.Real.Sqrt /- √ -/

/-!
# 3. The area element

A *fundamental form* is a rule that combines two vectors `v` and `w` of the tangent plane at a point
into a number `B(v, w)`, linearly in each and without regard to order, as the dot product does. This
is called a *symmetric bilinear form* on each tangent plane. On a patch every tangent vector is a
combination `v = h σᵤ + k σᵥ`, so by linearity a fundamental form is recorded by three numbers, its
values on `σᵤ` and `σᵥ`. For instance,

  `B(v, v) = h² B(σᵤ, σᵤ) + 2hk B(σᵤ, σᵥ) + k² B(σᵥ, σᵥ)`.

A surface has two fundamental forms that matter. The *first* measures lengths and angles within
the surface, and the *second*, in `4-GaussianCurvature`, measures how the surface bends in `ℝ³`.
They are fundamental in the sense that together they determine the surface up to a rigid motion
(Pressley, Theorem 10.1.3; do Carmo, Section 4-3). A third, the dot product of the derivatives of
the normal, is determined by the first two and is not needed here.

The *first fundamental form* is the dot product of tangent vectors (Pressley, Definition 6.1.1). On
a patch it is recorded by

  `E = σᵤ · σᵤ`,  `F = σᵤ · σᵥ`,  `G = σᵥ · σᵥ`.

It determines the *area element* `dA = ‖σᵤ × σᵥ‖ = √(EG - F²)` (Definition 6.4.1 and
Proposition 6.4.2), by which the area of `σ(R)` is `∫∫_R ‖σᵤ × σᵥ‖ du dv`. The direction of
`σᵤ × σᵥ` is the unit normal `N` of `2-Orientation`.

In Lean, `∫∫_R f du dv` is Mathlib's `∫ x in R, f x`, the Lebesgue integral over `R ⊆ ℝ²`. Mathlib
returns `0` for a function that is not integrable, so an integral is only meaningful when the
integrand is. Every integral in this library is over a bounded region whose closure lies in `U`,
and its integrand is continuous there, so it is integrable.

Each quantity belongs to a patch `σ` and is written with dot notation, as in `σ.E q` or
`σ.areaElement q`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S) (q : ℝ²)

/-- `E = σᵤ · σᵤ` -/
noncomputable def E : ℝ := ⟪σᵤ q, σᵤ q⟫

/-- `F = σᵤ · σᵥ` -/
noncomputable def F : ℝ := ⟪σᵤ q, σᵥ q⟫

/-- `G = σᵥ · σᵥ` -/
noncomputable def G : ℝ := ⟪σᵥ q, σᵥ q⟫

/-- **The area element** `dA = ‖σᵤ × σᵥ‖` -/
noncomputable def areaElement : ℝ :=
  ‖cross (σᵤ q) (σᵥ q)‖

/-- `‖σᵤ × σᵥ‖ = √(EG - F²)` (Pressley, Proposition 6.4.2) -/
theorem areaElement_eq_sqrt : σ.areaElement q = √(σ.E q * σ.G q - σ.F q ^ 2) :=
  sorry

end SurfacePatch
