import Mathlib.Analysis.Calculus.LineDeriv.Basic /- lineDeriv -/
import Mathlib.Analysis.InnerProductSpace.PiL2 /- EuclideanSpace, EuclideanSpace.single -/
import Mathlib.Analysis.Normed.Lp.WithLp /- WithLp.toLp -/
import Mathlib.LinearAlgebra.CrossProduct /- crossProduct -/

/-!
# Notation

The notation used throughout the library, so that statements read as they do on paper.

* `ℝ²` and `ℝ³`, the plane of parameters and the space containing the surface
* `e₁` and `e₂`, the directions of increasing `u` and `v`
* `∂ᵤ f` and `∂ᵥ f`, partial derivatives
* `σᵤ`, `σᵥ`, `σᵤᵤ`, `σᵤᵥ`, and `σᵥᵥ`, the partial derivatives of a patch `σ`
* `cross a b`, the cross product `a × b` in `ℝ³`
-/

/-- `ℝ²`, the plane of parameters `(u, v)`. Mathlib calls it `EuclideanSpace ℝ (Fin 2)`. Its
points are functions from `Fin 2 = {0, 1}` to `ℝ`, and `‖·‖` is the Euclidean norm. -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `ℝ³`, the space that contains the surface -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `e₁ = (1, 0)`, the direction of increasing `u` -/
notation "e₁" => (EuclideanSpace.single 0 1 : ℝ²)

/-- `e₂ = (0, 1)`, the direction of increasing `v` -/
notation "e₂" => (EuclideanSpace.single 1 1 : ℝ²)

/-- `∂ᵤ f q`, the partial derivative of `f` with respect to `u` at `q`. It is Mathlib's line
derivative of `f` in the direction `e₁`. -/
noncomputable def partialU {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ² → X) (q : ℝ²) : X :=
  lineDeriv ℝ f q e₁

/-- `∂ᵥ f q`, the partial derivative of `f` with respect to `v` at `q` -/
noncomputable def partialV {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ² → X) (q : ℝ²) : X :=
  lineDeriv ℝ f q e₂

@[inherit_doc] prefix:max "∂ᵤ " => partialU
@[inherit_doc] prefix:max "∂ᵥ " => partialV

/-! ## Partial derivatives of a patch

A subscript is part of a Lean name, so `σᵤ` cannot mean `σ` with a subscript `u`. Instead each of
the following is notation for a derivative of whatever is named `σ` where it is used, which
throughout this library is the surface patch. Turning off hygiene is what lets the notation refer
to that `σ`. The unexpanders below print the derivatives back in the same notation, in goals as
well as in statements. -/

set_option hygiene false in
/-- `σᵤ = ∂ᵤ σ` -/
notation "σᵤ" => ∂ᵤ σ

set_option hygiene false in
/-- `σᵥ = ∂ᵥ σ` -/
notation "σᵥ" => ∂ᵥ σ

set_option hygiene false in
/-- `σᵤᵤ = ∂ᵤ ∂ᵤ σ` -/
notation "σᵤᵤ" => ∂ᵤ (∂ᵤ σ)

set_option hygiene false in
/-- `σᵤᵥ = ∂ᵥ ∂ᵤ σ` -/
notation "σᵤᵥ" => ∂ᵥ (∂ᵤ σ)

set_option hygiene false in
/-- `σᵥᵥ = ∂ᵥ ∂ᵥ σ` -/
notation "σᵥᵥ" => ∂ᵥ (∂ᵥ σ)

open Lean PrettyPrinter in
/-- Prints `∂ᵤ ↑σ` as `σᵤ` and `∂ᵤ σᵤ` as `σᵤᵤ` -/
@[app_unexpander partialU] def unexpandPartialU : Unexpander
  | `($_ ↑$f:ident) => if f.getId == `σ then `(σᵤ) else throw ()
  | `($_ σᵤ) => `(σᵤᵤ)
  | _ => throw ()

open Lean PrettyPrinter in
/-- Prints `∂ᵥ ↑σ` as `σᵥ`, `∂ᵥ σᵤ` as `σᵤᵥ`, and `∂ᵥ σᵥ` as `σᵥᵥ` -/
@[app_unexpander partialV] def unexpandPartialV : Unexpander
  | `($_ ↑$f:ident) => if f.getId == `σ then `(σᵥ) else throw ()
  | `($_ σᵤ) => `(σᵤᵥ)
  | `($_ σᵥ) => `(σᵥᵥ)
  | _ => throw ()

/-- `a × b`, the cross product. Mathlib's `crossProduct` acts on `Fin 3 → ℝ`, the coordinates of a
point of `ℝ³`. -/
noncomputable def cross (a b : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (crossProduct a.ofLp b.ofLp)
