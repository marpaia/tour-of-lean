module

public import Surfaces.«5-GeodesicCurvature» /- geodesicCurvature, OrthonormalFrame, K, areaElement -/
public import Surfaces.«2-Orientation» /- orientedAngle -/
public import Surfaces.Notation /- ℝ², ℝ³, ∂ᵤ, ∂ᵥ, cross -/
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs /- ∑ -/
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace /- MeasurableSpace ℝ² -/
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
public import Mathlib.LinearAlgebra.LinearIndependent.Defs /- LinearIndependent -/
public import Mathlib.Logic.Equiv.Fin.Rotate /- finRotate -/
public import Mathlib.MeasureTheory.Integral.Bochner.Basic /- ∫ x in R, f x -/
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic /- ∫ s in a..b, f s -/
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis /- volume on ℝ² -/
public import Mathlib.Tactic.Linarith.Frontend /- linarith -/
public import Mathlib.Topology.Bornology.Basic /- Bornology.IsBounded -/
public import Mathlib.Topology.Connected.Basic /- connectedComponentIn -/
public import Mathlib.Topology.Defs.Filter /- 𝓝[>] -/

/-!
# 6. Local Gauss–Bonnet

A *curvilinear polygon* is a simple closed curve made of smooth sides `c₀, …, cₙ₋₁` that meet at
corners. On a patch, the sides trace arcs `γⱼ = σ ∘ cⱼ` on the surface, bounding a region `R`. Local
Gauss–Bonnet (Pressley, Theorem 13.2.2; do Carmo, Section 4-5) says that the geodesic curvature of
the arcs, the Gaussian curvature inside, and the exterior angles at the corners add up to `2π`,

  `Σⱼ ∫ κg ds + ∫∫_R K dA + Σⱼ δⱼ = 2π`.

The proof measures the turning of the tangent against an orthonormal frame `e′, e″`. By
`5-GeodesicCurvature`, the tangent angle turns at the rate `θ̇ = κg + e′ · ė″`.

* *Hopf's Umlaufsatz.* Going once around a simple closed curve, the tangent turns through `2π`.
  Along the arcs it turns by `∫ κg ds + ∮ e′ · de″`, and at the corners by `Σⱼ δⱼ`.
* *The frame rotates by the total curvature.* Green's theorem turns `∮ e′ · de″` into the
  integral over `R` of the *curl* `e′ᵤ · e″ᵥ - e′ᵥ · e″ᵤ`, and the curl is `K` times the area
  element.

Subtracting the second from the first leaves Gauss–Bonnet. Neither Hopf's Umlaufsatz nor Green's
theorem for general regions is in Mathlib.

Sides are curves in the plane, and arcs are their images on the surface. Side `j` ends where side
`j + 1` begins, with indices taken mod `n`. Mathlib's `finRotate n j` is this next index.
-/

@[expose] public section

open scoped ContDiff Topology RealInnerProductSpace Real

/-- **Curvilinear polygons** (Pressley, Definition 13.2.1). A simple closed curve in the plane
made of `n` smooth sides, where side `j` runs from `cⱼ(0)` to `cⱼ(ℓⱼ)` and makes a genuine corner
with the next side. -/
structure CurvilinearPolygon where
  /-- the number of sides -/
  numSides : ℕ
  /-- the sides `cⱼ` -/
  side : Fin numSides → ℝ → ℝ²
  /-- the lengths `ℓⱼ` of the parameter intervals `[0, ℓⱼ]` -/
  sideLength : Fin numSides → ℝ
  /-- `ℓⱼ > 0` -/
  sideLength_pos : ∀ j, 0 < sideLength j
  /-- each side is smooth -/
  smooth : ∀ j, ContDiff ℝ ∞ (side j)
  /-- each side ends where the next begins -/
  closes : ∀ j, side j (sideLength j) = side (finRotate numSides j) 0
  /-- each point of the polygon is reached exactly once, counting each corner as the start of the
  side that leaves it -/
  simple : ∀ j k, ∀ s ∈ Set.Ico 0 (sideLength j), ∀ s' ∈ Set.Ico 0 (sideLength k),
    side j s = side k s' → j = k ∧ s = s'
  /-- at each corner, the arriving and leaving velocities are not parallel -/
  corner : ∀ j,
    LinearIndependent ℝ ![deriv (side j) (sideLength j), deriv (side (finRotate numSides j)) 0]

namespace CurvilinearPolygon

variable (P : CurvilinearPolygon)

/-- The points of the polygon -/
def trace : Set ℝ² :=
  ⋃ j, P.side j '' Set.Icc 0 (P.sideLength j)

/-- **The inside** `R`. The points off the polygon whose region of the complement is bounded. The
Jordan curve theorem, which is not in Mathlib, says that there is exactly one such region. -/
def inside : Set ℝ² :=
  {x | x ∉ P.trace ∧ Bornology.IsBounded (connectedComponentIn P.traceᶜ x)}

/-- **Positive orientation.** Along each side, the velocity `(a, b)` turned anticlockwise by
`π / 2`, which is `(-b, a)`, points inside. -/
def IsPositivelyOriented : Prop :=
  ∀ j, ∀ s ∈ Set.Ioo 0 (P.sideLength j),
    let v := deriv (P.side j) s
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.side j s + ε • !₂[-v 1, v 0] ∈ P.inside

/-- **The line integral** `∮ f du + g dv` around the polygon -/
noncomputable def lineIntegral (f g : ℝ² → ℝ) : ℝ :=
  ∑ j, ∫ s in (0)..P.sideLength j,
    let c := P.side j
    f (c s) * deriv c s 0 + g (c s) * deriv c s 1

/-- **Green's theorem** (Pressley, Section 3.2). `∮ f du + g dv = ∫∫_R (gᵤ - fᵥ) du dv` around a
positively oriented polygon. -/
theorem lineIntegral_eq_integral (oriented : P.IsPositivelyOriented) {f g : ℝ² → ℝ} {O : Set ℝ²}
    (open_O : IsOpen O) (subset_O : closure P.inside ⊆ O)
    (smooth_f : ContDiffOn ℝ ∞ f O) (smooth_g : ContDiffOn ℝ ∞ g O) :
    P.lineIntegral f g = ∫ x in P.inside, (∂ᵤ g x - ∂ᵥ f x) :=
  sorry

end CurvilinearPolygon

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S)

/-- **Curvilinear polygons on a patch** (Pressley, Section 13.2). A positively oriented curvilinear
polygon lying, together with its inside, in `U`. -/
structure Polygon extends CurvilinearPolygon where
  /-- the polygon is positively oriented -/
  positivelyOriented : toCurvilinearPolygon.IsPositivelyOriented
  /-- the polygon and its inside lie in `U` -/
  closure_inside_subset : closure toCurvilinearPolygon.inside ⊆ σ.U

namespace Polygon

variable {σ} (P : σ.Polygon)

/-- The arc `γⱼ = σ ∘ cⱼ` on the surface traced by side `j` -/
def arc (j : Fin P.numSides) : ℝ → ℝ³ :=
  σ ∘ P.side j

/-- **Unit speed.** Every arc has `‖γ̇ⱼ‖ = 1`, so `ℓⱼ` is its length. -/
def IsUnitSpeed : Prop :=
  ∀ j, ∀ s ∈ Set.Icc 0 (P.sideLength j), ‖deriv (P.arc j) s‖ = 1

/-- **Total geodesic curvature** `Σⱼ ∫ κg ds` of the arcs -/
noncomputable def totalGeodesicCurvature : ℝ :=
  ∑ j, ∫ s in (0)..P.sideLength j, σ.geodesicCurvature (P.side j) s

/-- **Total curvature** `∫∫_R K dA` of the region inside -/
noncomputable def totalCurvature : ℝ :=
  ∫ x in P.inside, σ.K x * σ.areaElement x

/-- **The exterior angle** `δⱼ` at the corner where arc `j` ends, the oriented angle from the
arriving velocity to the leaving velocity -/
noncomputable def exteriorAngle (j : Fin P.numSides) : ℝ :=
  let arriving := deriv (P.arc j) (P.sideLength j)
  let leaving := deriv (P.arc (finRotate P.numSides j)) 0
  σ.orientedAngle (P.side j (P.sideLength j)) arriving leaving

end Polygon

namespace OrthonormalFrame

variable {σ} (frame : σ.OrthonormalFrame)

/-- **The curl of the frame** `e′ᵤ · e″ᵥ - e′ᵥ · e″ᵤ` -/
noncomputable def curl (q : ℝ²) : ℝ :=
  ⟪∂ᵤ frame.e' q, ∂ᵥ frame.e'' q⟫ - ⟪∂ᵥ frame.e' q, ∂ᵤ frame.e'' q⟫

/-- **The curl of the frame is the curvature** (Pressley, Lemma 13.1.3).
`e′ᵤ · e″ᵥ - e′ᵥ · e″ᵤ = K ‖σᵤ × σᵥ‖`. -/
theorem curl_eq_K_mul_areaElement {q : ℝ²} (q_in_U : q ∈ σ.U) :
    frame.curl q = σ.K q * σ.areaElement q :=
  sorry

/-- **The rotation of the frame** `∮ e′ · de″` around a polygon -/
noncomputable def rotationAround (P : σ.Polygon) : ℝ :=
  ∑ j, ∫ s in (0)..P.sideLength j,
    let c := P.side j
    ⟪frame.e' (c s), deriv (frame.e'' ∘ c) s⟫

/-- **The frame rotates by the total curvature.** By the chain rule `∮ e′ · de″` is the line
integral of `e′ · e″ᵤ du + e′ · e″ᵥ dv`, Green's theorem turns it into the integral of the curl,
and the curl is `K dA`. -/
theorem rotationAround_eq_totalCurvature (P : σ.Polygon) :
    frame.rotationAround P = P.totalCurvature :=
  sorry

end OrthonormalFrame

variable {σ}

/-- **Hopf's Umlaufsatz** (Pressley, Theorem 3.1.4 and Equation 13.12). Going once around the
polygon, the tangent turns through `2π`. Measured against the frame, it turns by
`∫ κg ds + ∮ e′ · de″` along the arcs and by `δⱼ` at each corner. -/
theorem Polygon.hopf_umlaufsatz {P : σ.Polygon} (unit_speed : P.IsUnitSpeed)
    (frame : σ.OrthonormalFrame) :
    P.totalGeodesicCurvature + frame.rotationAround P + ∑ j, P.exteriorAngle j = 2 * π :=
  sorry

/-- **Local Gauss–Bonnet** (Pressley, Theorem 13.2.2; do Carmo, Section 4-5).
`Σⱼ ∫ κg ds + ∫∫_R K dA + Σⱼ δⱼ = 2π`. -/
theorem Polygon.gauss_bonnet {P : σ.Polygon} (unit_speed : P.IsUnitSpeed) :
    P.totalGeodesicCurvature + P.totalCurvature + ∑ j, P.exteriorAngle j = 2 * π := by
  obtain ⟨frame⟩ := σ.nonempty_orthonormalFrame
  have turning := P.hopf_umlaufsatz unit_speed frame
  have rotation := frame.rotationAround_eq_totalCurvature P
  linarith

end SurfacePatch
