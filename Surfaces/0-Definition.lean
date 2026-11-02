import Mathlib.Algebra.Group.Hom.Basic /- injective_iff_map_eq_zero -/
import Mathlib.Analysis.Calculus.ContDiff.Defs /- ContDiffOn, ∞ -/
import Mathlib.Analysis.Calculus.FDeriv.Basic /- DifferentiableOn.differentiableAt -/
import Mathlib.Analysis.Calculus.FDeriv.Defs /- fderiv -/
import Mathlib.Analysis.Calculus.LineDeriv.Basic /- lineDeriv -/
import Mathlib.Analysis.InnerProductSpace.PiL2 /- EuclideanSpace -/
import Mathlib.Data.Set.Function /- Function.invFunOn -/
import Mathlib.Data.Set.Operations /- Set.InjOn -/
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas /- LinearIndependent.pair_iff -/
import Mathlib.Tactic.FinCases /- fin_cases -/
import Mathlib.Topology.ContinuousOn /- ContinuousOn.mapsToRestrict -/
import Mathlib.Topology.Defs.Basic /- IsOpen -/
import Mathlib.Topology.Defs.Filter /- ContinuousOn -/
import Mathlib.Topology.Homeomorph.Defs /- Homeomorph -/
import Mathlib.Topology.Neighborhoods /- IsOpen.mem_nhds -/

/-!
# The definition of a surface

Pressley, *Elementary Differential Geometry*, 2nd ed., states the definition in two stages. The
first is topological.

Definition 4.1.1, p. 68:

A subset `S` of `ℝ³` is a *surface* if, for every point `p ∈ S`, there is an open set `U`
in `ℝ²` and an open set `W` in `ℝ³` containing `p` such that `S ∩ W` is homeomorphic
to `U`. A homeomorphism `σ : U → S ∩ W` as in this definition is called a *surface patch*.

The second adds calculus.

Definition 4.2.1, p. 77:

A surface patch `σ : U → ℝ³` is called *regular* if it is smooth and the vectors `σ_u` and `σ_v`
are linearly independent at all points `(u, v) ∈ U`.

Definition 4.2.2, p. 77:

If `S` is a surface, an *allowable surface patch* for `S` is a regular surface patch
`σ : U → ℝ³` such that `σ` is a homeomorphism from `U` to an open subset of `S`. A
*smooth surface* is a surface `S` such that, for any point `p ∈ S`, there is an allowable surface
patch `σ` as above such that `p ∈ σ(U)`.

Do Carmo, *Differential Geometry of Curves and Surfaces*, states the same definition in one
stage.

Section 2-2, Definition 1, p. 54:

A subset `S ⊂ ℝ³` is a *regular surface* if, for each `p ∈ S`, there exists a neighborhood `V` in
`ℝ³` and a map `x : U → V ∩ S` of an open set `U ⊂ ℝ²` onto `V ∩ S ⊂ ℝ³` such that
1. `x` is differentiable.
2. `x` is a homeomorphism.
3. (The regularity condition.) For each `q ∈ U`, the differential `dx_q : ℝ² → ℝ³` is one-to-one.

Taken together, the two definitions make eight requirements at each point `p` of `S`, and each
one is a Mathlib predicate.

1. `U` is open (`IsOpen U`).
2. `W` is open and `σ` maps `U` onto `S ∩ W` (`IsOpen W` and `σ '' U = S ∩ W`).
3. Every point of `S` lies in the window of some patch (`∀ p ∈ S, ∃ σ, p ∈ σ.W`).
4. `σ` is one-to-one (`Set.InjOn σ U`).
5. `σ` is continuous (`ContinuousOn σ U`).
6. `σ⁻¹` is continuous (`ContinuousOn (Function.invFunOn σ U) (S ∩ W)`).
7. `σ` is smooth (`ContDiffOn ℝ ∞ σ U`).
8. `dσ_q` is one-to-one (`Function.Injective (fderiv ℝ σ q)`).

The file ends with two checks that these fields say what the books say. Parts 2, 4, 5, and 6 make
`σ` a homeomorphism `U ≃ₜ S ∩ W`, and do Carmo's Condition 3 is Pressley's linear independence of
`σ_u` and `σ_v`.
-/

/-- `ℝ²`, the plane of parameters `(u, v)`. Mathlib calls it `EuclideanSpace ℝ (Fin 2)`. Its
points are functions from `Fin 2 = {0, 1}` to `ℝ`, and `‖·‖` is the Euclidean norm. -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `ℝ³`, the space that contains the surface -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped ContDiff

/-- **Surface patches** (Pressley, Definition 4.1.1). A map `σ : U → S ∩ W` satisfying parts 1, 2,
4, 5, and 6, which together say that `σ` is a homeomorphism from an open `U ⊆ ℝ²` onto the piece of
`S` inside an open `W ⊆ ℝ³`. -/
structure SurfacePatch (S : Set ℝ³) where
  /-- `σ(u, v)` -/
  toFun : ℝ² → ℝ³
  /-- `U ⊆ ℝ²` -/
  U : Set ℝ²
  /-- `W ⊆ ℝ³` -/
  W : Set ℝ³
  /-- Part 1: `U` is open, so every point of `U` is the centre of an open ball inside `U` -/
  isOpen_U : IsOpen U
  /-- Part 2: `W` is open -/
  isOpen_W : IsOpen W
  /-- Part 2: `σ(U) = S ∩ W`, where `σ '' U` is Mathlib's notation for the image `σ(U)` -/
  image_eq : toFun '' U = S ∩ W
  /-- Part 4: `σ` is one-to-one -/
  injOn : Set.InjOn toFun U
  /-- Part 5: `σ` is continuous -/
  continuousOn : ContinuousOn toFun U
  /-- Part 6: `σ⁻¹` is continuous. `Function.invFunOn σ U y` is a parameter in `U` that `σ` sends
  to `y`, and by Part 4 it is the only one. -/
  continuousOn_invFunOn : ContinuousOn (Function.invFunOn toFun U) (S ∩ W)

/-- **Surfaces** (Pressley, Definition 4.1.1). Part 3: every point of `S` lies in the window of
some surface patch. -/
def IsSurface (S : Set ℝ³) : Prop :=
  ∀ p ∈ S, ∃ σ : SurfacePatch S, p ∈ σ.W

/-- **Allowable patches** (Pressley, Definitions 4.2.1 and 4.2.2). A surface patch that also
satisfies parts 7 and 8. -/
structure AllowablePatch (S : Set ℝ³) extends SurfacePatch S where
  /-- Part 7: `σ` is smooth -/
  contDiffOn : ContDiffOn ℝ ∞ toFun U
  /-- Part 8: `dσ_q` is one-to-one, where `fderiv ℝ σ q : ℝ² → ℝ³` is the linear map that best
  approximates `σ` near `q` -/
  injective_fderiv : ∀ q ∈ U, Function.Injective (fderiv ℝ toFun q)

/-- **Smooth surfaces** (Pressley, Definition 4.2.2; do Carmo's *regular surfaces*). Part 3 again:
every point of `S` lies in the window of some allowable patch. -/
def IsSmoothSurface (S : Set ℝ³) : Prop :=
  ∀ p ∈ S, ∃ σ : AllowablePatch S, p ∈ σ.W

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S)

/-- **`S ∩ W` is homeomorphic to `U`** (Pressley, Definition 4.1.1). Mathlib's `U ≃ₜ (S ∩ W)` is a
bijection that is continuous in both directions. `MapsTo.restrict` views `σ` as a map from `U` to
`S ∩ W`. -/
noncomputable def toHomeomorph : σ.U ≃ₜ ↑(S ∩ σ.W) :=
  have mapsTo : Set.MapsTo σ.toFun σ.U (S ∩ σ.W) := by
    rw [← σ.image_eq]
    exact Set.mapsTo_image _ _
  have surjOn : Set.SurjOn σ.toFun σ.U (S ∩ σ.W) := by
    rw [← σ.image_eq]
    exact Set.surjOn_image _ _
  have mapsTo_inv : Set.MapsTo (Function.invFunOn σ.toFun σ.U) (S ∩ σ.W) σ.U :=
    fun _ y_in_piece => Function.invFunOn_mem (surjOn y_in_piece)
  { toFun := mapsTo.restrict
    invFun := mapsTo_inv.restrict
    left_inv := fun x => Subtype.ext (σ.injOn.leftInvOn_invFunOn x.2)
    right_inv := fun y => Subtype.ext (surjOn.rightInvOn_invFunOn y.2)
    continuous_toFun := σ.continuousOn.mapsToRestrict mapsTo
    continuous_invFun := σ.continuousOn_invFunOn.mapsToRestrict mapsTo_inv }

end SurfacePatch

/-- `e₁ = (1, 0)`, the first vector of do Carmo's canonical basis of `ℝ²` (Section 2-2, p. 55) -/
notation "e₁" => (EuclideanSpace.single 0 1 : ℝ²)

/-- `e₂ = (0, 1)`, the second vector of do Carmo's canonical basis of `ℝ²` -/
notation "e₂" => (EuclideanSpace.single 1 1 : ℝ²)

/-- `x = x₀ e₁ + x₁ e₂` -/
theorem eq_smul_e₁_add_smul_e₂ (x : ℝ²) : x = x 0 • e₁ + x 1 • e₂ := by
  ext i
  fin_cases i <;> simp

/-- A linear map `L : ℝ² → ℝ³` is one-to-one exactly when `L(e₁)` and `L(e₂)` are linearly
independent. -/
theorem injective_iff_linearIndependent (L : ℝ² →L[ℝ] ℝ³) :
    Function.Injective L ↔ LinearIndependent ℝ ![L e₁, L e₂] := by
  rw [
    injective_iff_map_eq_zero,
    LinearIndependent.pair_iff
  ]
  constructor
  · intro kernel_trivial s t combination
    -- `s e₁ + t e₂` is sent to `0`, so it is `0`, and its coordinates `s` and `t` are `0`.
    have zero := kernel_trivial (s • e₁ + t • e₂) (by simpa using combination)
    have s_eq : s = 0 := by simpa using congrArg (· 0) zero
    have t_eq : t = 0 := by simpa using congrArg (· 1) zero
    exact ⟨s_eq, t_eq⟩
  · intro independent x x_to_zero
    -- `L(x) = x₀ L(e₁) + x₁ L(e₂) = 0`, so both coordinates of `x` are `0`.
    rw [eq_smul_e₁_add_smul_e₂ x] at x_to_zero ⊢
    obtain ⟨x₀_eq, x₁_eq⟩ := independent (x 0) (x 1) (by simpa using x_to_zero)
    rw [
      x₀_eq,
      x₁_eq
    ]
    simp

/-- **Do Carmo's regularity is Pressley's** (Definition 4.2.1). `σ_u` is the velocity of the
`u`-coordinate curve `t ↦ σ(q + t e₁)`, which Mathlib calls the line derivative
`lineDeriv ℝ σ q e₁`, and likewise `σ_v = lineDeriv ℝ σ q e₂`. Since `σ_u = dσ_q(e₁)` and
`σ_v = dσ_q(e₂)`, Part 8 makes them linearly independent. -/
theorem AllowablePatch.linearIndependent {S : Set ℝ³} (σ : AllowablePatch S) {q : ℝ²}
    (hq : q ∈ σ.U) :
    LinearIndependent ℝ ![lineDeriv ℝ σ.toFun q e₁, lineDeriv ℝ σ.toFun q e₂] := by
  -- `σ` is differentiable at `q`, because it is smooth on `U` and `U` is open.
  have differentiable : DifferentiableAt ℝ σ.toFun q :=
    (σ.contDiffOn.differentiableOn (by simp)).differentiableAt (σ.isOpen_U.mem_nhds hq)
  rw [
    differentiable.lineDeriv_eq_fderiv,
    differentiable.lineDeriv_eq_fderiv
  ]
  exact (injective_iff_linearIndependent _).mp (σ.injective_fderiv q hq)
