/-
# Orthogonality

Two vectors are *orthogonal* — perpendicular — when their inner product is zero:

    ⟪u, v⟫_ℝ = 0.

That one equation is the seed of a surprising amount of geometry. This file
gathers orthogonality's basic facts and, more importantly, its two
*characterizations* — the two other ways of saying "perpendicular" that the rest
of this directory has been circling:

  * **by angle**: `u` and `v` are orthogonal exactly when the angle between them
    is a right angle, `angle u v = π/2`;
  * **by Pythagoras**: `u` and `v` are orthogonal exactly when their squared
    lengths add, `‖u + v‖² = ‖u‖² + ‖v‖²`.

So orthogonality is the hub where the angle of `Geometry.Angle` and the
Pythagorean theorem of `Geometry.PythagoreanTheorem` meet: each is just
`⟪u, v⟫_ℝ = 0` wearing different clothes. We import both files and use *their*
results — `angle` and `pythagorean_theorem` — so the connections are real rather
than narrated.

The Pythagorean characterization is worth singling out. `PythagoreanTheorem`
proved only one direction: orthogonal ⟹ the squared lengths add. Here we supply
the converse — if the lengths add, the cross term `2⟪u, v⟫` in the bilinear
expansion must have vanished, so `⟪u, v⟫ = 0` — upgrading that theorem to a full
*if and only if*.

## A note on how we say "orthogonal"

We phrase everything in terms of the bare equation `⟪u, v⟫_ℝ = 0` rather than
wrapping it in a predicate. That was a real choice, and it is worth recording the
alternatives, because the same trade-off recurs whenever a concept is "just an
equation."

**The options were:**

  1. *Raw equation* (what we do): state every theorem about `⟪u, v⟫_ℝ = 0`.
  2. *A predicate* — `def Orthogonal (u v : F) : Prop := ⟪u, v⟫_ℝ = 0` — and
     phrase theorems as `Orthogonal u v ↔ …`.
  3. *A predicate with notation*, additionally writing `u ⟂ v`.

**What Mathlib does** is decide this three different ways, by object:

  * For *two vectors* in an inner product space it uses the **raw equation** —
    and even bakes it into the lemma *names* (`inner_eq_zero_symm`,
    `inner_eq_zero_of_left`, `…_iff_real_inner_eq_zero`).
  * For *submodules* it defines a **predicate with notation**, `Submodule.IsOrtho
    U V`, written `U ⟂ V` — because `U ⟂ V` unfolds to `∀ u ∈ U, ∀ v ∈ V,
    ⟪u, v⟫ = 0`, which is *not* a single equation, so the name carries real
    content.
  * For *bilinear forms* it defines a **predicate with a full API**,
    `BilinForm.IsOrtho B x y` (plus `isOrtho_def`, commutativity under `IsRefl`/
    `IsSymm`, indexed families, …) — because there orthogonality is an object of
    *study*, not a one-off hypothesis.

The principle: **name orthogonality when it is either not expressible as one
equation (submodules) or an object of structural study (bilinear forms); leave it
as `⟪u, v⟫ = 0` when it is a plain relation between two concrete vectors.** Our
setting is the last one, so we follow Mathlib and stay raw.

**Why not the predicate here.** A `def Orthogonal := ⟪u, v⟫_ℝ = 0` is opaque to
the very tactics that do our work: `rw`, `linarith`, and the substitution
`pythagorean_theorem` performs on its hypothesis all act on the *equation*, and a
predicate would have to be unfolded at every such boundary. Marking it
`reducible` to dodge that only moves the problem — it then unfolds in the *goal
display* too, so the pretty name `u ⟂ v` you wanted vanishes from view. You can
have transparency to tactics *or* a visible name, not both; Mathlib buys
transparency by not naming it (for vectors), and pays for the name with a lemma
API only where the name earns its keep.

This is *not* in tension with `Geometry.Angle` defining its own `angle`. `angle`
packages a non-trivial *construction* — the `arccos` of a normalized inner
product — whose value matters and which Mathlib itself makes a `def`.
Orthogonality would wrap a trivial one-equation *proposition*, exactly the thing
Mathlib declines to name for vectors. Name the construction; leave the equation.

And making orthogonality "first-class" never needed a wrapper: giving it its own
file, with the characterizations gathered and explained, is what does that.
Mathlib treats orthogonality as central without a vector predicate, and so do we.

## The setting

We work over an arbitrary real inner-product space `F`:

  * `[SeminormedAddCommGroup F]` — vectors add, negate, and carry a *seminorm*
    `‖·‖` (a length not required to be definite);
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied to
    the seminorm by `⟪x, x⟫_ℝ = ‖x‖²`.

As with the theorems it gathers, none of the characterizations below uses
*definiteness* (`‖x‖ = 0 → x = 0`), so they live over a *seminorm* — the weakest
setting `InnerProductSpace` requires. (The null case of the angle bridge even
leans on `inner_eq_zero_of_left`, a Mathlib lemma stated for `‖x‖ = 0` rather
than `x = 0` precisely so it survives the dropping of definiteness.) No dimension
or coordinate is named either, so "orthogonal" means the same thing in the plane,
in `ℝⁿ`, and in infinite-dimensional spaces alike.
-/

import Geometry.Angle
import Geometry.PythagoreanTheorem

-- `open scoped InnerProductSpace` enables `⟪x, y⟫_𝕜`; `open Real` enables `π`.
open scoped InnerProductSpace
open Real

namespace Geometry

/-! We fix an arbitrary real inner-product space `F` for the whole file, the same
setting as the theorems this one builds on. -/
variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Orthogonality is symmetric.** `⟪u, v⟫_ℝ = 0` exactly when `⟪v, u⟫_ℝ = 0`:
being perpendicular does not depend on the order of the two vectors, because the
real inner product is symmetric (`real_inner_comm`). -/
theorem inner_eq_zero_comm (u v : F) : ⟪u, v⟫_ℝ = 0 ↔ ⟪v, u⟫_ℝ = 0 := by
  -- `real_inner_comm` flips `⟪u, v⟫` to `⟪v, u⟫`, after which both sides of the
  -- `↔` are the same equation.
  rw [real_inner_comm]

/-- **Orthogonal ⟺ right angle.** Two vectors are orthogonal exactly when the
angle between them is `π/2`. This is the bridge to `Geometry.Angle`: it unfolds
the angle to its `arccos` and uses that `arccos x = π/2 ↔ x = 0`. -/
theorem inner_eq_zero_iff_angle_eq_pi_div_two (u v : F) :
    ⟪u, v⟫_ℝ = 0 ↔ angle u v = π / 2 := by
  -- Expose the `arccos` in `angle`, then `arccos x = π/2 ↔ x = 0` turns the
  -- right-angle condition into the vanishing of the *normalized* inner product
  -- `⟪u, v⟫ / (‖u‖‖v‖)`.
  unfold angle
  rw [Real.arccos_eq_pi_div_two]
  constructor
  · -- If `⟪u, v⟫ = 0` the numerator is `0`, so the whole ratio is `0`.
    intro h
    rw [h, zero_div]
  · -- Conversely the ratio vanishes only if its numerator does — or its
    -- denominator does, but `‖u‖‖v‖ = 0` forces one vector to be `0`, which makes
    -- the inner product `0` anyway (`inner_eq_zero_of_left`/`_of_right`).
    intro h
    rcases div_eq_zero_iff.mp h with h0 | h0
    · exact h0
    · rcases mul_eq_zero.mp h0 with hu | hv
      · exact inner_eq_zero_of_left v hu
      · exact inner_eq_zero_of_right u hv

/-- **Orthogonal ⟺ Pythagoras.** Two vectors are orthogonal exactly when the
squared norm of their sum is the sum of their squared norms. The forward
direction *is* our `pythagorean_theorem`; the converse, proved here, is what
turns that one-way theorem into a characterization. -/
theorem inner_eq_zero_iff_norm_add_sq (u v : F) :
    ⟪u, v⟫_ℝ = 0 ↔ ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  constructor
  · -- Forward: this is precisely the Pythagorean theorem we already proved.
    intro h
    exact pythagorean_theorem u v h
  · -- Converse: expand `‖u + v‖²` by bilinearity into `‖u‖² + 2⟪u, v⟫ + ‖v‖²`.
    -- Setting that equal to `‖u‖² + ‖v‖²` leaves `2⟪u, v⟫ = 0`, so `⟪u, v⟫ = 0`.
    intro h
    have expand : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        inner_add_right, real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v,
        real_inner_comm u v]
      ring
    linarith

/-! ### The same theorems in Mathlib

Each result here has a Mathlib counterpart. Symmetry is `inner_eq_zero_symm`,
with both vectors implicit: -/

example (u v : F) : ⟪u, v⟫_ℝ = 0 ↔ ⟪v, u⟫_ℝ = 0 := inner_eq_zero_symm

/-! The Pythagorean characterization is
`norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`. It runs in the
opposite direction, with the norm equation on the left, so recovering our
statement means flipping it with `Iff.symm` and rewriting its `‖·‖ * ‖·‖` into
our `‖·‖ ^ 2`: -/

example (u v : F) :
    ⟪u, v⟫_ℝ = 0 ↔ ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [pow_two, pow_two, pow_two]
  exact (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero u v).symm

/-! The angle characterization is Mathlib's
`InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`, the same statement
under the same name. As with `Geometry.Angle`, that namespace assumes a
`NormedAddCommGroup`, so it cannot be applied to this file's seminormed `F`
directly. Restricting to a normed space, where the definiteness it assumes holds,
our statement is exactly its statement: -/

example {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] (u v : G) :
    ⟪u, v⟫_ℝ = 0 ↔ angle u v = π / 2 :=
  InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two u v

end Geometry
