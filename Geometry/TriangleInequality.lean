/-
# The triangle inequality

The triangle inequality says that no detour through a third point is ever
shorter than going straight: the length of one side of a triangle never exceeds
the sum of the other two. In the language of vectors, with the third vertex
placed at the origin and the two sides recorded as `u` and `v`, the side joining
their tips is `u + v`, and the claim becomes

    ‖u + v‖ ≤ ‖u‖ + ‖v‖.

This file proves exactly that, in an arbitrary real inner-product space. The
mathematics is short; the instructional point is *theorem chaining*. The
triangle inequality is not proved from scratch — it falls out of the
Cauchy–Schwarz inequality, and we use *our own* proof of it: this file `import`s
`Analysis.CauchySchwarz` and calls its `cauchy_schwarz` theorem directly, so the
dependency is real rather than narrated. We expand a squared norm, drop in
Cauchy–Schwarz to bound the one term we cannot compute exactly, and the
inequality assembles itself.

## The arc: Pythagoras, Cauchy–Schwarz, and the triangle inequality

All three theorems begin from the same bilinear expansion of a squared length:

    ‖u + v‖² = ‖u‖² + 2⟪u, v⟫_ℝ + ‖v‖²

Everything turns on what we can say about the cross term `⟪u, v⟫_ℝ`.

  * In the **Pythagorean theorem** the hypothesis is *orthogonality*: the cross
    term is exactly **zero**, so the squared lengths add and we get `‖u + v‖² =
    ‖u‖² + ‖v‖²`.
  * In general the cross term is not zero, but it is never larger than it could
    possibly be: **Cauchy–Schwarz** says `⟪u, v⟫_ℝ ≤ ‖u‖ ‖v‖`. The cross term
    is *bounded* rather than *vanishing*.
  * Feeding that bound back into the expansion replaces `2⟪u, v⟫_ℝ` by its
    ceiling `2‖u‖‖v‖`, and the right-hand side collapses into a perfect square:

        ‖u + v‖² ≤ ‖u‖² + 2‖u‖‖v‖ + ‖v‖² = (‖u‖ + ‖v‖)².

    Taking (nonnegative) square roots gives the **triangle inequality**.

So Pythagoras and the triangle inequality are the two ends of one calculation:
when the cross term is zero the squared lengths add exactly; when it is merely
bounded the lengths add only up to an inequality. Equality holds precisely when
the cross term hits its Cauchy–Schwarz ceiling — when `u` and `v` point the same
way — which is the degenerate triangle flattened onto a line.

## Isn't this already built into the norm?

It is — and seeing why we prove it anyway is half the lesson. The setting below
opens with `[SeminormedAddCommGroup F]`, and a seminormed group does not merely
carry a seminorm; it carries one that *already* obeys `‖u + v‖ ≤ ‖u‖ + ‖v‖` (the
triangle inequality is one of the seminorm axioms, definiteness is not). Mathlib
even names that promise — `norm_add_le` — and `exact norm_add_le u v` would close
this file's goal on its first line. So what is the inner-product proof *for*?

A fact and its *provenance* are different things. In the bundled setting
`[SeminormedAddCommGroup F] [InnerProductSpace ℝ F]` the seminorm is handed to us
ready-made, and the inner product only *links* to it through the bridge
`⟪x, x⟫ = ‖x‖²`; here the triangle inequality holds by assumption, and the proof
below re-derives a fact the typeclasses already guaranteed.

But there is a more primitive starting point at which nothing about length is
assumed at all. Give Mathlib only an inner product — the bilinearity of
`Bilinearity.lean`, its symmetry, and the lone positivity `0 ≤ ⟪x, x⟫` — and
*define* a candidate length by `‖x‖ := √⟪x, x⟫`. Now `‖·‖` is just a formula, and
nothing yet entitles it to be called a length. Most of the seminorm laws — `‖0‖ =
0`, `‖-x‖ = ‖x‖`, homogeneity — follow by direct algebra from the inner product;
exactly one needs the detour through Cauchy–Schwarz, and that one is the triangle
inequality. The only way to earn it is the calculation in this file: recast
`‖u + v‖²` as an inner product, bound its cross term with Cauchy–Schwarz, and
watch the right-hand side close into the perfect square `(‖u‖ + ‖v‖)²`. Those
laws together make `√⟪x, x⟫` a genuine *seminorm* — which is exactly the setting
this file works in, and why definiteness never appears. The one law left out,
*definiteness* (`‖x‖ = 0 → x = 0`), is the single thing a seminorm may lack; it
holds only when the inner product is itself definite (`⟪x, x⟫ = 0 → x = 0`), the
extra axiom separating a `PreInnerProductSpace.Core` (which Mathlib promotes to a
*seminormed* space) from an `InnerProductSpace.Core` (which `InnerProductSpace.ofCore`
promotes to a *normed* one). Either way the triangle-inequality field is proved
from the core's Cauchy–Schwarz lemma by the very squared-norm argument we run below.

So the proof reads two ways at once. In the setting we work in it re-proves a
promised fact — a clean specimen of the theorem chaining this file is here to
teach. In the construction that *builds* a norm from an inner product it is
load-bearing: the step that turns the formula `√⟪x, x⟫` into a genuine length,
and so the precise sense in which "an inner product induces a norm" is a theorem
to be proved and not a slogan to be repeated.

## The setting

We work over an arbitrary type `F` carrying two pieces of structure:

  * `[SeminormedAddCommGroup F]` — vectors can be added, negated, and measured by
    a *seminorm* `‖·‖`: a length not required to be definite, so a nonzero vector
    may still have `‖x‖ = 0`.
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied to
    the seminorm by `⟪x, x⟫_ℝ = ‖x‖²`.

Neither this proof nor the Cauchy–Schwarz it leans on uses *definiteness*, so the
seminorm — the weakest setting `InnerProductSpace` requires — is all we assume
(matching Mathlib's `Norm_Seminormed` section). No dimension or coordinate is ever
mentioned either, so the theorem holds in the plane, in `ℝⁿ`, and in
infinite-dimensional spaces alike.

## The argument

Both sides of `‖u + v‖ ≤ ‖u‖ + ‖v‖` are nonnegative, so the inequality is
equivalent to the comparison of their squares,

    ‖u + v‖² ≤ (‖u‖ + ‖v‖)²,

and that squared form is where the inner-product machinery and Cauchy–Schwarz
do their work. We prove the squared inequality, then convert back to the linear
one by a lemma that says a square comparison between numbers of the right sign
lifts to a comparison of the numbers themselves.
-/

import Analysis.CauchySchwarz

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Geometry

/-! We fix an arbitrary real inner-product space `F` for the whole file. Stating
the constraints once with `variable` lets the theorem below inherit them
automatically; Lean inserts only the binders a declaration actually mentions. -/
variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Triangle inequality.** The length of a sum never exceeds the sum of the
lengths.

The proof is a reduction followed by a chain. First we reduce to comparing
squares, because `abs_le_of_sq_le_sq'` turns a squared inequality back into the
linear one. Then a `calc` expands `‖u + v‖²` by bilinearity and bounds its cross
term with Cauchy–Schwarz, landing on the perfect square `(‖u‖ + ‖v‖)²`. -/
theorem triangle_inequality (u v : F) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  /- Both sides are nonnegative: norms are nonnegative (`norm_nonneg`), and a
     sum of nonnegatives is nonnegative (`add_nonneg`). We name the right-hand
     side's nonnegativity now because the square-root step below requires it. -/
  have hsum_nonneg : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg u) (norm_nonneg v)
  /- The heart of the proof: the squared inequality. Once we have it, lifting it
     to the linear statement is a single lemma. -/
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    calc ‖u + v‖ ^ 2
        /- A norm and its inner product are two views of the same quantity:
           `⟪w, w⟫ = ‖w‖²`. We take the inner-product view so that bilinearity
           can expand the sum. That identity is `real_inner_self_eq_norm_sq`. -/
        = ⟪u + v, u + v⟫_ℝ := by
            rw [real_inner_self_eq_norm_sq]
        /- An inner product is linear in each argument, so we multiply out
           `(u + v)·(u + v)`. `inner_add_left` distributes over the first slot;
           `inner_add_right`, applied to each resulting term, distributes over
           the second, leaving the four pairwise inner products. -/
      _ = ⟪u, u⟫_ℝ + ⟪u, v⟫_ℝ + (⟪v, u⟫_ℝ + ⟪v, v⟫_ℝ) := by
            rw [inner_add_left, inner_add_right, inner_add_right]
        /- The two self-pairings fold back into squared norms (reading
           `real_inner_self_eq_norm_sq` the other way), and the two cross terms
           are equal because the real inner product is symmetric
           (`real_inner_comm`). This collects them into a single `2 * ⟪u, v⟫`. -/
      _ = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v,
              real_inner_comm v u]
            ring
        /- Here Cauchy–Schwarz enters — our own `cauchy_schwarz`, imported from
           the `Analysis` foundations. It gives the *absolute-value* bound
           `|⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖`, which is strictly stronger than what we need:
           the cross term itself is at most its own absolute value
           (`le_abs_self`), so chaining the two with `le_trans` yields the
           one-sided bound `⟪u, v⟫_ℝ ≤ ‖u‖ * ‖v‖`. Replacing the cross term by
           that ceiling turns the middle term `2⟪u, v⟫` into `2‖u‖‖v‖`, and the
           whole right-hand side is then the expansion of a perfect square.
           `nlinarith` discharges this: it multiplies the bound through by the
           positive constant `2` and recognizes `(‖u‖ + ‖v‖)²` on the other
           side. -/
      _ ≤ (‖u‖ + ‖v‖) ^ 2 := by
            nlinarith [le_trans (le_abs_self ⟪u, v⟫_ℝ) (Analysis.cauchy_schwarz u v)]
  /- Finally we descend from squares to lengths. `abs_le_of_sq_le_sq'` takes a
     squared inequality `a² ≤ b²` together with `0 ≤ b` and returns the pair
     `-b ≤ a ∧ a ≤ b`; the second component is exactly `‖u + v‖ ≤ ‖u‖ + ‖v‖`. -/
  exact (abs_le_of_sq_le_sq' hsq hsum_nonneg).2

end Geometry
