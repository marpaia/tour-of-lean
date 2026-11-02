module

public import Surfaces.Notation /- ℝ², ℝ³ -/
public import Mathlib.Analysis.Calculus.ContDiff.Defs /- ContDiffOn, ∞ -/
public import Mathlib.Analysis.Calculus.FDeriv.Defs /- fderiv -/
public import Mathlib.Data.Set.Function /- Function.invFunOn -/
public import Mathlib.Data.Set.Operations /- Set.InjOn -/
public import Mathlib.Topology.Defs.Basic /- IsOpen -/
public import Mathlib.Topology.Defs.Filter /- ContinuousOn -/

/-!
# 0. Smooth surfaces

A *smooth surface* is a set `S ⊆ ℝ³` whose every point lies in the window of a *surface patch*.
A patch is a map `σ` from an open set of parameters `U ⊆ ℝ²` onto the piece `S ∩ W` of the surface
cut out by an open window `W ⊆ ℝ³`. The definition has eight parts, each a Mathlib predicate.

1. `U` is open.
2. `W` is open, and `σ` maps `U` onto `S ∩ W`.
3. Every point of `S` lies in the window of some patch.
4. `σ` is one-to-one.
5. `σ` is continuous.
6. `σ⁻¹` is continuous.
7. `σ` is smooth.
8. The derivative `dσ_q` is one-to-one at every `q ∈ U`.

Parts 2, 4, 5, and 6 say that `σ` is a homeomorphism from `U` onto `S ∩ W` (Pressley,
Definition 4.1.1), and parts 7 and 8 add calculus. Part 8 is do Carmo's regularity condition
(Section 2-2, Definition 1). It is equivalent to Pressley's requirement that `σᵤ` and `σᵥ` be
linearly independent (Definition 4.2.1), and Pressley calls a patch satisfying all of these
*allowable* (Definition 4.2.2).
-/

@[expose] public section

open scoped ContDiff

/-- **Surface patches.** A map `σ : U → S ∩ W` satisfying parts 1, 2, and 4 to 8. -/
structure SurfacePatch (S : Set ℝ³) where
  /-- `σ(u, v)` -/
  toFun : ℝ² → ℝ³
  /-- `U ⊆ ℝ²` -/
  U : Set ℝ²
  /-- `W ⊆ ℝ³` -/
  W : Set ℝ³
  /-- Part 1: `U` is open, so every point of `U` is the centre of an open ball inside `U` -/
  open_U : IsOpen U
  /-- Part 2: `W` is open -/
  open_W : IsOpen W
  /-- Part 2: `σ(U) = S ∩ W`, where `σ '' U` is Mathlib's notation for the image `σ(U)` -/
  onto : toFun '' U = S ∩ W
  /-- Part 4: `σ` is one-to-one -/
  oneToOne : Set.InjOn toFun U
  /-- Part 5: `σ` is continuous -/
  continuous : ContinuousOn toFun U
  /-- Part 6: `σ⁻¹` is continuous. `Function.invFunOn σ U y` is a parameter in `U` that `σ` sends
  to `y`, and by Part 4 it is the only one. -/
  continuous_inverse : ContinuousOn (Function.invFunOn toFun U) (S ∩ W)
  /-- Part 7: `σ` is smooth -/
  smooth : ContDiffOn ℝ ∞ toFun U
  /-- Part 8: `dσ_q` is one-to-one, where `fderiv ℝ σ q : ℝ² → ℝ³` is the linear map that best
  approximates `σ` near `q` -/
  regular : ∀ q ∈ U, Function.Injective (fderiv ℝ toFun q)

attribute [coe] SurfacePatch.toFun

/-- A patch `σ` can be applied to a parameter `q` and written `σ q`, as in the books. -/
instance {S : Set ℝ³} : CoeFun (SurfacePatch S) fun _ => ℝ² → ℝ³ :=
  ⟨SurfacePatch.toFun⟩

/-- **Smooth surfaces** (Pressley, Definition 4.2.2; do Carmo's *regular surfaces*). Part 3: every
point of `S` lies in the window of some patch. -/
def IsSmoothSurface (S : Set ℝ³) : Prop :=
  ∀ p ∈ S, ∃ σ : SurfacePatch S, p ∈ σ.W
