import Surfaces.«1-TangentPlane» /- SurfacePatch, tangentPlane -/
import Surfaces.Notation /- σᵤ, σᵥ, cross -/
import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, y⟫ -/
import Mathlib.Basic.Real.Sign /- Real.sign -/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic /- InnerProductGeometry.angle -/
import Mathlib.Topology.ContinuousOn /- ContinuousOn -/

/-!
# 2. Orientation

A tangent plane by itself has no preferred sense of rotation. A unit vector `N` perpendicular to it
supplies one. Turning from `a` to `b` is *anticlockwise* when `a × b` points along `N`, as it does
in the plane `ℝ²` viewed from above, and the *oriented angle* from `a` to `b` is the angle between
them, positive for an anticlockwise turn and negative for a clockwise one.

A patch orients its tangent planes by its *unit normal* `N`, the direction of `σᵤ × σᵥ`. It carries
the anticlockwise sense of the parameter plane to the surface. It sends the directions `e₁` and
`e₂` to `σᵤ` and `σᵥ`, and turning from `σᵤ` to `σᵥ` is anticlockwise because `σᵤ × σᵥ` points along
`N` by definition. So a curve in `U` that turns anticlockwise traces a curve on the surface that
turns anticlockwise about `N`.

Two patches can orient the same tangent plane in opposite ways, because swapping `u` and `v`
reverses `N`. A surface is *orientable* if it has a continuous choice of unit normal at every
point, with patches agreeing with it around every point (Pressley, Section 4.5). Every compact
surface is orientable (Corollary 5.4.5). Global Gauss–Bonnet needs this, so that the patches of a
triangulation turn the same way where they meet.
-/

open scoped RealInnerProductSpace

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S)

/-- **The unit normal** `N = σᵤ × σᵥ / ‖σᵤ × σᵥ‖` (Pressley, Section 4.5) -/
noncomputable def normal (q : ℝ²) : ℝ³ :=
  ‖cross (σᵤ q) (σᵥ q)‖⁻¹ • cross (σᵤ q) (σᵥ q)

/-- **The oriented angle** from `a` to `b` in the tangent plane at `σ(q)`, between `-π` and `π`. Its
size is the angle between `a` and `b`, and its sign is positive when turning from `a` to `b` is
anticlockwise about `N`, that is, when `a × b` points along `N`. -/
noncomputable def orientedAngle (q : ℝ²) (a b : ℝ³) : ℝ :=
  Real.sign ⟪σ.normal q, cross a b⟫ * InnerProductGeometry.angle a b

/-- **The patch preserves orientation.** Turning from `σᵤ` to `σᵥ`, the images of `e₁` and `e₂`, is
anticlockwise about `N`. -/
theorem orientedAngle_σᵤ_σᵥ_pos {q : ℝ²} (q_in_U : q ∈ σ.U) : 0 < σ.orientedAngle q (σᵤ q) (σᵥ q) :=
  sorry

/-- **Patches oriented by a normal field.** The unit normal of `σ` agrees with the normal field
`n` on the surface. -/
def IsOrientedBy (n : ℝ³ → ℝ³) : Prop :=
  ∀ q ∈ σ.U, σ.normal q = n (σ q)

end SurfacePatch

/-- **Orientable surfaces** (Pressley, Section 4.5). A continuous unit normal field `n` on `S`, with
a patch oriented by it around every point. -/
def IsOrientable (S : Set ℝ³) : Prop :=
  ∃ n : ℝ³ → ℝ³, ContinuousOn n S ∧ ∀ p ∈ S, ∃ σ : SurfacePatch S, p ∈ σ.W ∧ σ.IsOrientedBy n

/-- **Compact surfaces are orientable** (Pressley, Corollary 5.4.5) -/
theorem IsSmoothSurface.isOrientable {S : Set ℝ³} (smooth : IsSmoothSurface S)
    (compact : IsCompact S) : IsOrientable S :=
  sorry
