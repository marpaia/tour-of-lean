/-
# The Cauchy–Schwarz inequality

The Cauchy–Schwarz inequality is the single most useful inequality in all of
analysis. It says that the inner product of two vectors can never exceed the
product of their lengths:

    |⟪u, v⟫| ≤ ‖u‖ · ‖v‖

In Euclidean space this is the familiar bound `|u · v| ≤ |u| |v|` that hides
behind `u · v = |u| |v| cos θ`: since `|cos θ| ≤ 1`, the dot product is always
squeezed between `±|u| |v|`. But Cauchy–Schwarz needs no angles and no cosines;
it holds in every real inner product space, finite-dimensional or not, and it is
in fact the inequality that *lets us define* the angle in the first place. It is
also the engine behind the triangle inequality for the norm, so it underlies the
very claim that `‖·‖` deserves to be called a length. Both of those consumers
live one layer up, in `Geometry` — `Geometry.Angle` and
`Geometry.TriangleInequality` import this file — which is why Cauchy–Schwarz sits
here among the `Analysis` foundations rather than with the geometry it makes
possible.

## The one idea: a length is never negative

Everything below is squeezed out of a single fact. For any vector `w`, its
self inner product is its squared length, and a squared length cannot be
negative:

    0 ≤ ⟪w, w⟫ = ‖w‖²

That is the only piece of "positivity" in the whole story. The trick is to apply
it not to one cleverly chosen `w` but to a whole *family*: for every real number
`t`, the vector `u - t • v` has nonnegative squared length. Expanding
`0 ≤ ⟪u - t•v, u - t•v⟫` by bilinearity gives, for every `t`,

    0 ≤ ‖v‖² · t² − 2⟪u, v⟫ · t + ‖u‖²,

a quadratic in `t` that never dips below zero. A quadratic `a t² + b t + c` that
stays nonnegative for *all* `t` cannot cross the axis, so its discriminant is
`≤ 0`:

    b² − 4ac ≤ 0,    i.e.    (2⟪u, v⟫)² ≤ 4 · ‖v‖² · ‖u‖²,

which rearranges to

    ⟪u, v⟫² ≤ ‖u‖² · ‖v‖².

That is the inequality in *squared* form; taking square roots — legal because
both sides are nonnegative — turns it into the absolute-value statement we want.

This is the classic *nonnegative-square* (or *discriminant*) argument, the
template for an enormous family of inequalities. Two things are worth noting
about this telling. First, it needs *no case split*: the discriminant step
swallows the degenerate `v` — where `‖v‖² = 0` and the quadratic is really
linear — without special handling, which is precisely what `discrim_le_zero`
does. Second, and for the same reason, it never *divides* by `⟪v, v⟫`, so it
never needs that quantity to be nonzero; that is what lets the whole argument run
over a mere *seminorm*, where a nonzero `v` may still have `‖v‖ = 0`.

## The setting

We work over an arbitrary type `F` carrying two pieces of structure:

  * `[SeminormedAddCommGroup F]` — vectors can be added, negated, and measured by
    a *seminorm* `‖·‖`: a length not required to be definite, so a nonzero vector
    may still have `‖x‖ = 0`.
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied to
    the seminorm by `⟪x, x⟫_ℝ = ‖x‖²`.

These two hypotheses are everything the proof uses — and the seminorm is the
weakest the inner product even admits, since `InnerProductSpace` is itself
declared over a seminormed group. The discriminant argument above is what lets us
stay here: it never divides by `⟪v, v⟫`, so it never needs *definiteness*
(`‖x‖ = 0 → x = 0`), and Cauchy–Schwarz lands in Mathlib's `Norm_Seminormed`
section rather than one floor up. Nothing below names a dimension or a coordinate
either, so the same theorem covers the plane, `ℝⁿ`, and infinite-dimensional
spaces alike.

## The argument

The proof has two movements:

  1. **Squared form.** Prove `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²`. Show first that for every
     `t` the expanded squared length `‖v‖² t² − 2⟪u, v⟫ t + ‖u‖²` is `≥ 0` — one
     bilinear expansion of `0 ≤ ⟪u - t•v, u - t•v⟫`, with `nlinarith` tidying it
     into that standard quadratic shape. Feed the whole family to
     `discrim_le_zero`, which returns `discriminant ≤ 0`; unfolding the
     discriminant and a second `nlinarith` rearrange that into the bound. No case
     split on `v`, and no division by `⟪v, v⟫`.

  2. **Take square roots.** From `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²` conclude
     `|⟪u, v⟫| ≤ ‖u‖ · ‖v‖`. The lemma `abs_le_of_sq_le_sq` does exactly this:
     given `a² ≤ b²` and `0 ≤ b`, it returns `|a| ≤ b`. Here `b = ‖u‖ · ‖v‖`,
     nonnegative because norms are, so `positivity` discharges that side
     condition on sight.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.QuadraticDiscriminant

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Analysis

/-! We fix an arbitrary real inner-product space `F` for the whole file. Stating
the constraints once with `variable` lets the theorem below inherit them
automatically; Lean inserts only the binders a declaration actually mentions. -/
variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Cauchy–Schwarz inequality.** The absolute value of the inner product of
two vectors is at most the product of their norms.

The proof first establishes the squared inequality `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²` from
the nonnegativity of a whole *family* of self inner products, then takes square
roots. -/
theorem cauchy_schwarz (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  /- **Movement 1: the squared form.** We isolate the key estimate
     `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²` as a local fact `key`; the rest of the proof is
     just extracting square roots from it. -/
  have key : ⟪u, v⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    /- The lone positivity input, applied to a whole family. For *every* real
       `t`, the vector `u - t • v` has nonnegative squared length. We expand that
       self inner product by bilinearity: `inner_sub_left`/`_right` distribute the
       subtraction across each slot, `real_inner_smul_left`/`_right` pull the
       scalar `t` out as multiplication, `real_inner_self_eq_norm_sq` folds each
       `⟪w, w⟫` into `‖w‖²`, and `real_inner_comm` merges the stray `⟪v, u⟫` with
       `⟪u, v⟫`. `nlinarith` then tidies the result into the standard quadratic
       shape `a·t² + b·t + c` that `discrim_le_zero` expects, with `a = ‖v‖²`,
       `b = −2⟪u, v⟫`, `c = ‖u‖²`. -/
    have hquad : ∀ t : ℝ,
        0 ≤ ‖v‖ ^ 2 * (t * t) + (-(2 * ⟪u, v⟫_ℝ)) * t + ‖u‖ ^ 2 := by
      intro t
      have h : 0 ≤ ⟪u - t • v, u - t • v⟫_ℝ := real_inner_self_nonneg
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_left,
        real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v,
        real_inner_comm u v] at h
      nlinarith [h]
    /- A quadratic that is `≥ 0` for *every* `t` cannot cross the axis, so its
       discriminant `b² − 4ac` is `≤ 0`. `discrim_le_zero` packages exactly that
       implication — and it absorbs the degenerate `‖v‖² = 0` (where the
       "quadratic" is really linear) with no separate case, which is what keeps
       the whole argument alive over a seminorm. -/
    have hdisc := discrim_le_zero hquad
    /- Unfold `discrim a b c = b² − 4ac`. With our `a`, `b`, `c`, `hdisc` becomes
       `(−2⟪u, v⟫)² − 4 · ‖v‖² · ‖u‖² ≤ 0`, and `nlinarith` divides through the
       constant `4` to land on `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²`. -/
    rw [discrim] at hdisc
    nlinarith [hdisc]
  /- **Movement 2: take square roots.** `abs_le_of_sq_le_sq` converts a squared
     inequality `a² ≤ b²` together with `0 ≤ b` into `|a| ≤ b`. We rewrite the
     right-hand side of `key` as `(‖u‖ * ‖v‖) ^ 2` so it has the form `b²`, then
     apply the lemma; `positivity` certifies `0 ≤ ‖u‖ * ‖v‖` from
     `norm_nonneg`. -/
  rw [← mul_pow] at key
  exact abs_le_of_sq_le_sq key (by positivity)

/-! ### The same theorem in Mathlib

Cauchy–Schwarz is already in Mathlib, as `abs_real_inner_le_norm`. It carries
this exact statement, in the same `Norm_Seminormed` section over the same
seminorm. The two vectors are explicit arguments, in order, so calling it is a
one-liner: -/

example (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v

/-! It comes in three forms, and picking the right one saves a step. The
absolute-value version above is the headline. `real_inner_le_norm u v` drops the
`|·|` to give the one-sided `⟪u, v⟫_ℝ ≤ ‖u‖ * ‖v‖` directly, usually what a bound
on a cross term wants. `norm_inner_le_norm` is the general version over any field,
`‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`; over `ℝ` the scalar norm is the absolute value, so it
collapses straight back to the statement we proved: -/

example (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) u v

end Analysis
