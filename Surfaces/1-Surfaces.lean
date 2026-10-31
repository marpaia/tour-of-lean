import Surfaces.«0-Topology» /- IsOpenSet, IsHomeomorphism -/
import Mathlib.Analysis.InnerProductSpace.PiL2 /- EuclideanSpace -/
import Mathlib.Basic.Real.Basic /- ℝ -/
import Mathlib.Data.Set.Basic /- Set, ∩ -/

/-!
# Surfaces

Pressley, *Elementary Differential Geometry*, 2nd ed., Definition 4.1.1, p. 68:

A subset `S` of `ℝ³` is a *surface* if, for every point `p ∈ S`, there is an open set `U`
in `ℝ²` and an open set `W` in `ℝ³` containing `p` such that `S ∩ W` is homeomorphic
to `U`. A subset of a surface `S` of the form `S ∩ W`, where `W` is an open subset
of `ℝ³`, is called an *open subset* of `S`. A homeomorphism `σ : U → S ∩ W` as in
this definition is called a *surface patch* or *parametrization* of the open subset
`S ∩ W` of `S`. A collection of such surface patches whose images cover the whole
of `S` is called an *atlas* of `S`.
-/

/-- `ℝ²` -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `ℝ³` -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A surface patch: a homeomorphism `σ : U → S ∩ W` with `U ⊆ ℝ²` and `W ⊆ ℝ³` open -/
structure SurfacePatch (S : Set ℝ³) where
  /-- `σ(u, v)` -/
  toFun : ℝ² → ℝ³
  /-- `U ⊆ ℝ²` -/
  U : Set ℝ²
  /-- `W ⊆ ℝ³` -/
  W : Set ℝ³
  /-- `U` is open -/
  isOpen_U : IsOpenSet U
  /-- `W` is open -/
  isOpen_W : IsOpenSet W
  /-- `σ : U → S ∩ W` is a homeomorphism -/
  isHomeomorphism : IsHomeomorphism toFun U (S ∩ W)

/-- `S` is a surface if every `P ∈ S` lies in the image of a surface patch -/
def IsSurface (S : Set ℝ³) : Prop :=
  ∀ P ∈ S,
    ∃ σ : SurfacePatch S,
      P ∈ σ.W
