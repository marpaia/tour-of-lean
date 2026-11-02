import Surfaces.«5-Curves» /- geodesicCurvature, K, areaElement -/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs /- ∑ -/
import Mathlib.Analysis.Calculus.Deriv.Basic /- HasDerivWithinAt -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- Real.pi -/
import Mathlib.Basic.Real.Sign /- Real.sign -/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic /- InnerProductGeometry.angle -/
import Mathlib.LinearAlgebra.LinearIndependent.Defs /- LinearIndependent -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic /- ∫ s in a..b, f s -/
import Mathlib.Order.Interval.Set.Defs /- Set.Ioo, Set.Iio, Set.Ioi -/
import Mathlib.Topology.Bornology.Basic /- Bornology.IsBounded -/
import Mathlib.Topology.Connected.Basic /- connectedComponentIn -/
import Mathlib.Topology.Defs.Filter /- 𝓝[>] -/

/-!
# 6. Local Gauss–Bonnet

A simple closed curve `γ = σ ∘ π` in a single patch encloses a region of the surface. Gauss–Bonnet
(Pressley, Theorem 13.1.2) says that the geodesic curvature around `γ` and the Gaussian curvature
inside it add up to `2π`.

  `∫ κg ds = 2π - ∫∫_{int γ} K dA`

The proof integrates `κg = θ̇ - e′ · ė″` from `5-Curves` around the curve. The term `θ̇` gives
`2π` by Hopf's Umlaufsatz (Theorem 3.1.4), because the tangent of a simple closed curve turns once.
Green's theorem (Section 3.2) turns the term `e′ · ė″` into the integral of `K` over the inside.
Neither theorem is in Mathlib for general simple closed curves.

A curvilinear polygon is a closed curve with corners. Each corner turns the tangent by an exterior
angle, and these angles join the formula (Theorem 13.2.2).
-/

open scoped ContDiff Topology RealInnerProductSpace

open Patch

/-- `w` rotated anticlockwise by `π / 2` -/
noncomputable def rotate (w : ℝ²) : ℝ² :=
  !₂[-(w 1), w 0]

/-- **Simple closed curves** (Pressley, Section 3.1). A smooth regular curve in the plane with
period `T`, which returns to a point only after a whole number of periods. -/
structure SimpleClosedCurve where
  /-- `π(t)` -/
  toFun : ℝ → ℝ²
  /-- the period -/
  T : ℝ
  /-- `T > 0` -/
  T_pos : 0 < T
  /-- `π` is smooth -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- `π(s) = π(s')` exactly when `s - s'` is a multiple of `T` -/
  eq_iff : ∀ s s', toFun s = toFun s' ↔ ∃ k : ℤ, s - s' = k * T
  /-- `π` is regular -/
  deriv_ne_zero : ∀ s, deriv toFun s ≠ 0

/-- **The inside of a closed curve.** The points off the curve whose region of the complement is
bounded. The Jordan curve theorem, which is not in Mathlib, says that there is exactly one such
region. -/
def inside (π : ℝ → ℝ²) : Set ℝ² :=
  {x | x ∉ Set.range π ∧ Bornology.IsBounded (connectedComponentIn (Set.range π)ᶜ x)}

/-- **Positive orientation** (Pressley, Section 13.1). At each smooth point, turning the velocity
anticlockwise by `π / 2` points inside. -/
def IsPositivelyOriented (π : ℝ → ℝ²) : Prop :=
  ∀ s, DifferentiableAt ℝ π s →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), π s + ε • rotate (deriv π s) ∈ inside π

/-- **Hopf's Umlaufsatz** (Pressley, Theorem 3.1.4). The tangent of a positively oriented simple
closed curve turns through exactly `2π`, so its total signed curvature is `2π`. -/
theorem hopf_umlaufsatz (π : SimpleClosedCurve) (oriented : IsPositivelyOriented π.toFun) :
    ∫ s in (0)..π.T,
        (deriv π.toFun s 0 * deriv (deriv π.toFun) s 1 -
          deriv π.toFun s 1 * deriv (deriv π.toFun) s 0) / ‖deriv π.toFun s‖ ^ 2 =
      2 * Real.pi :=
  sorry

/-- **Green's theorem** (Pressley, Section 3.2). Around a positively oriented simple closed curve,
`∮ P du + Q dv = ∫∫_{int π} (Q_u - P_v) du dv`. -/
theorem green (π : SimpleClosedCurve) (oriented : IsPositivelyOriented π.toFun)
    {P Q : ℝ² → ℝ} {O : Set ℝ²} (hO : IsOpen O) (closure_sub : closure (inside π.toFun) ⊆ O)
    (hP : ContDiffOn ℝ ∞ P O) (hQ : ContDiffOn ℝ ∞ Q O) :
    ∫ s in (0)..π.T,
        (P (π.toFun s) * deriv π.toFun s 0 + Q (π.toFun s) * deriv π.toFun s 1) =
      ∫ x in inside π.toFun, (∂ᵤ Q x - ∂ᵥ P x) :=
  sorry

/-- **Gauss–Bonnet for a simple closed curve** (Pressley, Theorem 13.1.2). If `γ = σ ∘ π` is
unit-speed, so that its period is its length, then `∫ κg ds = 2π - ∫∫_{int γ} K dA`. -/
theorem gauss_bonnet_simpleClosedCurve {S : Set ℝ³} (σ : AllowablePatch S)
    (π : SimpleClosedCurve) (oriented : IsPositivelyOriented π.toFun)
    (closure_sub : closure (inside π.toFun) ⊆ σ.U)
    (unit_speed : ∀ s, ‖deriv (σ.toFun ∘ π.toFun) s‖ = 1) :
    ∫ s in (0)..π.T, geodesicCurvature σ.toFun π.toFun s =
      2 * Real.pi - ∫ x in inside π.toFun, K σ.toFun x * areaElement σ.toFun x :=
  sorry

/-- **Curvilinear polygons** (Pressley, Definition 13.2.1). A closed curve with period `T` that is
smooth except at the vertices `π(t₁), …, π(tₙ)`, where it has one-sided velocities that are not
parallel. -/
structure CurvilinearPolygon where
  /-- `π(t)` -/
  toFun : ℝ → ℝ²
  /-- the period -/
  T : ℝ
  /-- the number of edges -/
  n : ℕ
  /-- the times `0 = t₀ < t₁ < ⋯ < tₙ = T` -/
  t : Fin (n + 1) → ℝ
  /-- `π` is continuous -/
  continuous : Continuous toFun
  /-- `π(s) = π(s')` exactly when `s - s'` is a multiple of `T` -/
  eq_iff : ∀ s s', toFun s = toFun s' ↔ ∃ k : ℤ, s - s' = k * T
  /-- `t₀ < t₁ < ⋯ < tₙ` -/
  strictMono : StrictMono t
  /-- `t₀ = 0` -/
  t_zero : t 0 = 0
  /-- `tₙ = T` -/
  t_last : t (Fin.last n) = T
  /-- `π` is smooth on each edge -/
  contDiffOn : ∀ j : Fin n, ContDiffOn ℝ ∞ toFun (Set.Ioo (t j.castSucc) (t j.succ))
  /-- the velocity arriving at the vertex `π(t_{j+1})` -/
  inDeriv : Fin n → ℝ²
  /-- the velocity leaving the vertex `π(t_{j+1})` -/
  outDeriv : Fin n → ℝ²
  /-- `π̇⁻(t_{j+1})` is the velocity arriving at the vertex -/
  hasDerivWithinAt_in : ∀ j, HasDerivWithinAt toFun (inDeriv j) (Set.Iio (t j.succ)) (t j.succ)
  /-- `π̇⁺(t_{j+1})` is the velocity leaving the vertex -/
  hasDerivWithinAt_out : ∀ j, HasDerivWithinAt toFun (outDeriv j) (Set.Ioi (t j.succ)) (t j.succ)
  /-- the two velocities at a vertex are not parallel -/
  not_parallel : ∀ j, LinearIndependent ℝ ![inDeriv j, outDeriv j]

/-- **The exterior angle at a vertex** (Pressley, Section 13.2). The signed angle on the surface
from the arriving velocity to the leaving velocity, positive when it turns anticlockwise about the
normal. -/
noncomputable def CurvilinearPolygon.exteriorAngle (σ : ℝ² → ℝ³) (P : CurvilinearPolygon)
    (j : Fin P.n) : ℝ :=
  let q := P.toFun (P.t j.succ)
  let a := fderiv ℝ σ q (P.inDeriv j)
  let b := fderiv ℝ σ q (P.outDeriv j)
  Real.sign ⟪normal σ q, cross a b⟫ * InnerProductGeometry.angle a b

/-- **Gauss–Bonnet for a curvilinear polygon** (Pressley, Theorem 13.2.2). With interior angles
`αⱼ = π - εⱼ`, `∫ κg ds = Σ αⱼ - (n - 2)π - ∫∫_{int γ} K dA`. -/
theorem gauss_bonnet_curvilinearPolygon {S : Set ℝ³} (σ : AllowablePatch S)
    (P : CurvilinearPolygon) (oriented : IsPositivelyOriented P.toFun)
    (closure_sub : closure (inside P.toFun) ⊆ σ.U)
    (unit_speed : ∀ j : Fin P.n, ∀ s ∈ Set.Ioo (P.t j.castSucc) (P.t j.succ),
      ‖deriv (σ.toFun ∘ P.toFun) s‖ = 1) :
    ∫ s in (0)..P.T, geodesicCurvature σ.toFun P.toFun s =
      ∑ j, (Real.pi - P.exteriorAngle σ.toFun j) - (P.n - 2) * Real.pi -
        ∫ x in inside P.toFun, K σ.toFun x * areaElement σ.toFun x :=
  sorry
