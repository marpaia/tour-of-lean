module

public import Surfaces.«0-Definition» /- SurfacePatch -/
public import Surfaces.Notation /- σᵤ, σᵥ -/
public import Mathlib.Analysis.Calculus.TangentCone.Defs /- tangentConeAt -/
public import Mathlib.LinearAlgebra.Dimension.Finrank /- Module.finrank -/
public import Mathlib.LinearAlgebra.Span.Defs /- Submodule.span -/

/-!
# 1. The tangent plane

A *tangent vector* to `S` at a point `p` is a direction in which `S` can be approached from `p`.
Pressley takes the velocities of curves in `S` through `p` (Definition 4.4.1). Mathlib's
`tangentConeAt ℝ S p` takes the limits of rescaled steps `c • d` with `p + d ∈ S` and `d → 0`,
which needs no curves and no patch.

On a patch, moving `u` and `v` gives the two velocities `σᵤ` and `σᵥ`, and every tangent vector is
a combination of them (Pressley, Proposition 4.4.2). We define the *tangent plane* at `σ(q)` as
their span, and state that it is exactly Mathlib's tangent cone, so that it depends only on the
surface. By Part 8, `σᵤ` and `σᵥ` are linearly independent, so the tangent plane is indeed a plane.
-/

@[expose] public section

namespace SurfacePatch

variable {S : Set ℝ³} (σ : SurfacePatch S)

/-- **The tangent plane** at `σ(q)`, the span of `σᵤ` and `σᵥ` -/
noncomputable def tangentPlane (q : ℝ²) : Submodule ℝ ℝ³ :=
  Submodule.span ℝ {σᵤ q, σᵥ q}

variable {q : ℝ²}

/-- **The tangent plane belongs to the surface** (Pressley, Proposition 4.4.2). Its vectors are
the tangent vectors to `S` at `σ(q)`, so every patch through `σ(q)` gives the same plane. -/
theorem tangentConeAt_eq_tangentPlane (q_in_U : q ∈ σ.U) :
    tangentConeAt ℝ S (σ q) = σ.tangentPlane q :=
  sorry

/-- **The tangent plane is two-dimensional**, because `σᵤ` and `σᵥ` are linearly independent
(Part 8). -/
theorem finrank_tangentPlane (q_in_U : q ∈ σ.U) : Module.finrank ℝ (σ.tangentPlane q) = 2 :=
  sorry

end SurfacePatch
