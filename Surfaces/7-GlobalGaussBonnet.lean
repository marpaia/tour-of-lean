module

public import Surfaces.«6-LocalGaussBonnet» /- SurfacePatch.Polygon, Polygon.totalCurvature -/
public import Surfaces.Notation /- ℝ³ -/
public import Surfaces.«2-Orientation» /- IsOrientedBy -/
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs /- ∑ -/
public import Mathlib.Data.Set.Card /- Set.ncard -/
public import Mathlib.Order.Interval.Set.Defs /- Set.Icc -/
public import Mathlib.Topology.Defs.Basic /- closure -/

/-!
# 7. Global Gauss–Bonnet

A *triangulation* cuts a compact surface into finitely many faces, each a polygon on a single
patch, that meet only along whole edges or at corners (Pressley, Definition 13.4.1). Its *Euler
number* is `χ = V - E + F`, the number of vertices minus the number of edges plus the number of
faces.

Adding up local Gauss–Bonnet over the faces, the geodesic curvature along each edge cancels, because
the two faces on either side run along it in opposite directions, and the exterior angles combine
with the `2π` from each face into `2π χ`. What remains is the Gauss–Bonnet theorem
(Theorem 13.4.5),

  `∫∫_S K dA = 2π χ`.
-/

@[expose] public section

open scoped Real

namespace SurfacePatch.Polygon

variable {S : Set ℝ³} {σ : SurfacePatch S} (P : σ.Polygon)

/-- The face `σ(closure R)`, the polygon together with its inside, on the surface -/
def face : Set ℝ³ :=
  σ '' closure P.inside

/-- The edges of the polygon on the surface, each the arc `γⱼ([0, ℓⱼ])` -/
def edges : Set (Set ℝ³) :=
  Set.range fun j => P.arc j '' Set.Icc 0 (P.sideLength j)

/-- The corners of the polygon on the surface -/
def vertices : Set ℝ³ :=
  Set.range fun j => P.arc j (P.sideLength j)

end SurfacePatch.Polygon

/-- **Triangulations** (Pressley, Definition 13.4.1). Finitely many faces, each a polygon on one
patch, such that the faces cover `S`, two faces meet in nothing, a common edge, or a common vertex,
and each edge belongs to exactly two faces. The patches are oriented alike, all oriented by one
normal field, which is possible on any compact surface by `IsSmoothSurface.isOrientable`. -/
structure Triangulation (S : Set ℝ³) where
  /-- the number of faces -/
  numFaces : ℕ
  /-- the patch carrying face `i` -/
  patch : Fin numFaces → SurfacePatch S
  /-- the polygon bounding face `i` -/
  polygon : (i : Fin numFaces) → (patch i).Polygon
  /-- the normal field orienting the surface -/
  normal : ℝ³ → ℝ³
  /-- every patch is oriented by `normal` -/
  orientedBy : ∀ i, (patch i).IsOrientedBy normal
  /-- the faces cover `S` -/
  covers : ⋃ i, (polygon i).face = S
  /-- two faces meet in nothing, a common edge, or a common vertex -/
  meet : ∀ i i', i ≠ i' →
    let A := (polygon i).face ∩ (polygon i').face
    A = ∅ ∨ A ∈ (polygon i).edges ∩ (polygon i').edges ∨
      ∃ v ∈ (polygon i).vertices ∩ (polygon i').vertices, A = {v}
  /-- each edge belongs to exactly two faces -/
  two_faces : ∀ i, ∀ e ∈ (polygon i).edges, {i' | e ∈ (polygon i').edges}.ncard = 2

namespace Triangulation

variable {S : Set ℝ³} (T : Triangulation S)

/-- The vertices of the triangulation -/
def vertices : Set ℝ³ :=
  ⋃ i, (T.polygon i).vertices

/-- The edges of the triangulation -/
def edges : Set (Set ℝ³) :=
  ⋃ i, (T.polygon i).edges

/-- **The Euler number** `χ = V - E + F` (Pressley, Definition 13.4.4) -/
noncomputable def eulerNumber : ℤ :=
  T.vertices.ncard - T.edges.ncard + T.numFaces

/-- **Total curvature** `∫∫_S K dA`, the sum of the total curvatures of the faces -/
noncomputable def totalCurvature : ℝ :=
  ∑ i, (T.polygon i).totalCurvature

/-- **Gauss–Bonnet** (Pressley, Theorem 13.4.5). `∫∫_S K dA = 2π χ` for any triangulation of a
compact smooth surface. -/
theorem gauss_bonnet (smooth : IsSmoothSurface S) (compact : IsCompact S) :
    T.totalCurvature = 2 * π * T.eulerNumber :=
  sorry

end Triangulation
