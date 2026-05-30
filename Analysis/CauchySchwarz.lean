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
very claim that `‖·‖` deserves to be called a length.

## The one idea: a length is never negative

Everything below is squeezed out of a single fact. For any vector `w`, its
self inner product is its squared length, and a squared length cannot be
negative:

    0 ≤ ⟪w, w⟫ = ‖w‖²

That is the only piece of "positivity" in the whole story. The trick is to feed
this fact a cleverly chosen `w` — a combination of `u` and `v` — and then let
the bilinearity of the inner product unpack `⟪w, w⟫` into a quadratic in `u`
and `v`. Demanding that this quadratic stay nonnegative is exactly the
Cauchy–Schwarz inequality. This is the classic *nonnegative-square* (or
*discriminant*) argument, and it is the template for an enormous family of
inequalities.

Concretely, when `v ≠ 0` we take

    w = u - t • v,    with    t = ⟪u, v⟫ / ⟪v, v⟫

— the part of `u` left over after subtracting its projection onto `v`. Expanding
`0 ≤ ⟪w, w⟫` by bilinearity gives, after clearing the denominator,

    ⟪u, v⟫² ≤ ⟪u, u⟫ · ⟪v, v⟫ = ‖u‖² · ‖v‖².

That is the inequality in *squared* form. Taking square roots — legal because
both sides are nonnegative — turns it into the absolute-value statement we want.

## The setting

We work over an arbitrary type `F` carrying two pieces of structure:

  * `[NormedAddCommGroup F]` — vectors can be added, negated, and measured:
    we have `+`, `0`, unary `-`, and a norm `‖·‖`.
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied
    to the norm by `⟪x, x⟫_ℝ = ‖x‖²`.

These two hypotheses are everything the proof uses. Nothing below names a
dimension or a coordinate, so the same theorem covers the plane, `ℝⁿ`, and
infinite-dimensional spaces alike.

## The argument

The proof has two movements:

  1. **Squared form.** Prove `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²`. Split on whether `v = 0`.
     If `v = 0` both sides collapse to `0`. Otherwise expand
     `0 ≤ ⟪u - t • v, u - t • v⟫` by bilinearity into a quadratic in `t`, then
     hand the whole thing to `nlinarith`, which finds the nonnegative
     combination of facts (including `0 ≤ ⟪v, v⟫` and the expanded square) that
     forces the bound.

  2. **Take square roots.** From `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²` conclude
     `|⟪u, v⟫| ≤ ‖u‖ · ‖v‖`. The lemma `abs_le_of_sq_le_sq` does exactly this:
     given `a² ≤ b²` and `0 ≤ b`, it returns `|a| ≤ b`. Here `b = ‖u‖ · ‖v‖`,
     nonnegative because norms are, so `positivity` discharges that side
     condition on sight.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Analysis

/-! We fix an arbitrary real inner-product space `F` for the whole file. Stating
the constraints once with `variable` lets the theorem below inherit them
automatically; Lean inserts only the binders a declaration actually mentions. -/
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Cauchy–Schwarz inequality.** The absolute value of the inner product of
two vectors is at most the product of their norms.

The proof first establishes the squared inequality `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²` from
the nonnegativity of a single self inner product, then takes square roots. -/
theorem cauchy_schwarz (u v : F) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  /- **Movement 1: the squared form.** We isolate the key estimate
     `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²` as a local fact `key`; the rest of the proof is
     just extracting square roots from it. -/
  have key : ⟪u, v⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    /- Split on whether `v` is the zero vector. `eq_or_ne v 0` hands us the two
       cases as a disjunction, and `rcases` names each branch. The degenerate
       case is what lets us divide by `⟪v, v⟫` safely in the main case. -/
    rcases eq_or_ne v 0 with hv | hv
    · /- If `v = 0`, substitute it everywhere. Both `⟪u, 0⟫` and `‖0‖` are zero,
         so each side of the inequality reduces to `0`, and `simp` closes the
         resulting `0 ≤ 0`. -/
      subst hv
      simp
    · /- The genuine case, `v ≠ 0`. The whole argument rests on one number being
         nonnegative: the squared length of `u - t • v` for the projection
         coefficient `t = ⟪u, v⟫ / ⟪v, v⟫`. We first record that this self inner
         product is `≥ 0` — the lone positivity input — via
         `real_inner_self_nonneg`. -/
      have hself : 0 ≤ ⟪u - (⟪u, v⟫_ℝ / ⟪v, v⟫_ℝ) • v,
          u - (⟪u, v⟫_ℝ / ⟪v, v⟫_ℝ) • v⟫_ℝ := real_inner_self_nonneg
      /- Now expand that self inner product by bilinearity. `inner_sub_left` and
         `inner_sub_right` distribute the subtraction across each slot, and
         `real_inner_smul_left` / `real_inner_smul_right` pull the scalar `t`
         out of the inner product as ordinary multiplication. After these
         rewrites `hself` is a concrete quadratic expression in the real numbers
         `⟪u, u⟫`, `⟪u, v⟫`, and `⟪v, v⟫`. -/
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_left] at hself
      /- Put `hself` into the same vocabulary as the goal. The goal speaks of
         `‖u‖`, `‖v‖`, and `⟪u, v⟫`, while `hself` is currently written with
         self inner products and a `⟪v, u⟫`. `real_inner_self_eq_norm_sq` turns
         each `⟪w, w⟫` into `‖w‖²`, and `real_inner_comm u v` flips the stray
         `⟪v, u⟫` into `⟪u, v⟫`. After this, `hself` and the goal share the same
         three quantities. -/
      rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v,
        real_inner_comm u v] at hself
      /- `‖v‖²` is strictly positive here: norms are nonnegative, and `‖v‖ ≠ 0`
         because `v ≠ 0`. We are about to divide by it, so we need it bounded
         away from zero. -/
      have hvv : 0 < ‖v‖ ^ 2 := by positivity
      /- `hself` still carries the denominator `‖v‖²` inside the coefficient `t`.
         `field_simp` clears all the divisions (justified by `hvv.ne'`, that
         `‖v‖² ≠ 0`), turning `hself` into a denominator-free polynomial
         inequality in `‖u‖²`, `‖v‖²`, and `⟪u, v⟫`. -/
      field_simp [hvv.ne'] at hself
      /- The finish. After clearing denominators, `hself` is a polynomial
         inequality that, once the squares are expanded, *is* the bound we want
         up to rearrangement. `nlinarith` finds the nonnegative combination of
         `hself` and the positivity `hvv` that proves
         `⟪u, v⟫² ≤ ‖u‖² · ‖v‖²`. -/
      nlinarith [hself, hvv, sq_nonneg (⟪u, v⟫_ℝ)]
  /- **Movement 2: take square roots.** `abs_le_of_sq_le_sq` converts a squared
     inequality `a² ≤ b²` together with `0 ≤ b` into `|a| ≤ b`. We rewrite the
     right-hand side of `key` as `(‖u‖ * ‖v‖) ^ 2` so it has the form `b²`, then
     apply the lemma; `positivity` certifies `0 ≤ ‖u‖ * ‖v‖` from
     `norm_nonneg`. -/
  rw [← mul_pow] at key
  exact abs_le_of_sq_le_sq key (by positivity)

end Analysis
