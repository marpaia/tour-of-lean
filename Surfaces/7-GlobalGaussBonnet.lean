import Surfaces.«6-LocalGaussBonnet» /- CurvilinearPolygon, inside, IsPositivelyOriented -/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs /- ∑ -/
import Mathlib.Data.Set.Card /- Set.ncard -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic /- ∫ x in R, f x -/
import Mathlib.Order.Disjoint /- Disjoint -/
import Mathlib.Order.Interval.Set.Defs /- Set.Icc -/
import Mathlib.Topology.Defs.Basic /- closure -/
import Mathlib.Topology.MetricSpace.Pseudo.Defs /- Metric.sphere -/

/-!
# 7. Global Gauss–Bonnet

A *triangulation* cuts a compact surface into finitely many curvilinear polygons, each inside a
single patch, that meet only along whole edges or at vertices (Pressley, Definition 13.4.1). Every
compact surface has one (Theorem 13.4.3), a theorem of Radó that is not in Mathlib.

Summing local Gauss–Bonnet over the polygons, the geodesic curvature along each interior edge
cancels, because the two polygons on either side traverse it in opposite directions. What remains
is the Gauss–Bonnet theorem (Theorem 13.4.5).

  `∫∫_S K dA = 2π χ`

The left side does not depend on the triangulation, so neither does the Euler number
`χ = V - E + F` (Corollary 13.4.6).
-/

open Patch

variable {S : Set ℝ³}

/-- The face `σ(π ∪ int π)` of a polygon `π` in a patch `σ` -/
def face (σ : AllowablePatch S) (P : CurvilinearPolygon) : Set ℝ³ :=
  σ.toFun '' closure (inside P.toFun)

/-- The `j`-th edge, from `π(tⱼ)` to `π(t_{j+1})`, on the surface -/
def edge (σ : AllowablePatch S) (P : CurvilinearPolygon) (j : Fin P.n) : Set ℝ³ :=
  σ.toFun '' (P.toFun '' Set.Icc (P.t j.castSucc) (P.t j.succ))

/-- The vertex `π(t_{j+1})`, on the surface -/
def vertex (σ : AllowablePatch S) (P : CurvilinearPolygon) (j : Fin P.n) : ℝ³ :=
  σ.toFun (P.toFun (P.t j.succ))

/-- **Triangulations** (Pressley, Definition 13.4.1). Finitely many positively oriented
curvilinear polygons, each lying with its inside in one patch, such that the faces cover `S`, two
faces are disjoint or meet in exactly one common edge or vertex, and each edge belongs to exactly
two faces. -/
structure Triangulation (S : Set ℝ³) where
  /-- the number of polygons -/
  m : ℕ
  /-- the patch containing the `i`-th polygon -/
  patch : Fin m → AllowablePatch S
  /-- the `i`-th polygon, in the parameters of its patch -/
  polygon : Fin m → CurvilinearPolygon
  /-- each polygon is positively oriented -/
  oriented : ∀ i, IsPositivelyOriented (polygon i).toFun
  /-- each polygon lies, with its inside, in its patch -/
  closure_sub : ∀ i, closure (inside (polygon i).toFun) ⊆ (patch i).U
  /-- (i) the faces cover `S` -/
  covers : (⋃ i, face (patch i) (polygon i)) = S
  /-- (ii) two faces are disjoint, or meet in a common edge, or meet in a common vertex -/
  meet : ∀ i i', i ≠ i' →
    Disjoint (face (patch i) (polygon i)) (face (patch i') (polygon i')) ∨
    (∃ j j', edge (patch i) (polygon i) j = edge (patch i') (polygon i') j' ∧
      face (patch i) (polygon i) ∩ face (patch i') (polygon i') = edge (patch i) (polygon i) j) ∨
    (∃ j j', vertex (patch i) (polygon i) j = vertex (patch i') (polygon i') j' ∧
      face (patch i) (polygon i) ∩ face (patch i') (polygon i') = {vertex (patch i) (polygon i) j})
  /-- (iii) each edge is an edge of exactly two faces -/
  two_faces : ∀ i j, {i' | ∃ j', edge (patch i') (polygon i') j' =
    edge (patch i) (polygon i) j}.ncard = 2

namespace Triangulation

variable (𝒯 : Triangulation S)

/-- The points of `S` that are vertices of the triangulation -/
def vertices : Set ℝ³ :=
  ⋃ i, Set.range (vertex (𝒯.patch i) (𝒯.polygon i))

/-- The subsets of `S` that are edges of the triangulation -/
def edges : Set (Set ℝ³) :=
  ⋃ i, Set.range (edge (𝒯.patch i) (𝒯.polygon i))

/-- **The Euler number** `χ = V - E + F` (Pressley, Definition 13.4.4) -/
noncomputable def eulerNumber : ℤ :=
  𝒯.vertices.ncard - 𝒯.edges.ncard + 𝒯.m

/-- **Total curvature** `∫∫_S K dA`, the sum of the integrals of `K` over the faces -/
noncomputable def totalCurvature : ℝ :=
  ∑ i, ∫ x in inside (𝒯.polygon i).toFun, K (𝒯.patch i).toFun x * areaElement (𝒯.patch i).toFun x

end Triangulation

/-- **Compact surfaces can be triangulated** (Pressley, Theorem 13.4.3) -/
theorem nonempty_triangulation (compact : IsCompact S) (smooth : IsSmoothSurface S) :
    Nonempty (Triangulation S) :=
  sorry

/-- **Gauss–Bonnet** (Pressley, Theorem 13.4.5). `∫∫_S K dA = 2π χ` for any triangulation of a
compact surface. -/
theorem gauss_bonnet (compact : IsCompact S) (𝒯 : Triangulation S) :
    𝒯.totalCurvature = 2 * Real.pi * 𝒯.eulerNumber :=
  sorry

/-- **The Euler number is a property of the surface** (Pressley, Corollary 13.4.6). Any two
triangulations of a compact surface have the same Euler number. -/
theorem eulerNumber_eq (compact : IsCompact S) (𝒯 𝒯' : Triangulation S) :
    𝒯.eulerNumber = 𝒯'.eulerNumber :=
  sorry

/-- **The sphere has Euler number `2`** (Pressley, Example 13.4.2 and Theorem 13.4.5). Its
curvature is `1 / r²` and its area is `4π r²`, so `∫∫ K dA = 4π`. -/
theorem eulerNumber_sphere {r : ℝ} (hr : 0 < r) (𝒯 : Triangulation (Metric.sphere (0 : ℝ³) r)) :
    𝒯.eulerNumber = 2 :=
  sorry
