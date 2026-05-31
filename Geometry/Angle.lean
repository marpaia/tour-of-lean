/-
# Length and angle from the inner product

A single inner product `⟪·, ·⟫_ℝ` quietly carries *both* halves of Euclidean
geometry — how long a vector is, and how two vectors are angled apart. This file
makes that precise: it recovers length and angle from the inner product alone,
and shows that the one fact standing between the definition of "angle" and
nonsense is the Cauchy–Schwarz inequality proved in `Analysis.CauchySchwarz`.

## Length comes for free

The length half needs no work: the norm is *defined* so that its square is the
self inner product, so

    ‖u‖ = √⟪u, u⟫.

That is the Mathlib lemma `norm_eq_sqrt_real_inner` — the same `⟪w, w⟫ = ‖w‖²`
bridge the other proofs use, read through a square root. There is no theorem to
prove here; length is simply how the inner product was wired to the norm.

## Angle is *defined* — and Cauchy–Schwarz is what makes the definition legal

The angle half is different in kind. In an abstract inner product space there is
no prior notion of angle to prove things about. Instead the cosine identity is
turned around and used as the *definition*:

    angle u v := arccos (⟪u, v⟫ / (‖u‖ ‖v‖)).

But `arccos` is only defined on `[-1, 1]`. For this definition to mean anything,
its argument must land in that interval:

    -1 ≤ ⟪u, v⟫ / (‖u‖ ‖v‖) ≤ 1     ⟺     |⟪u, v⟫| ≤ ‖u‖ ‖v‖,

and the right-hand side is *exactly* Cauchy–Schwarz. So the inequality is not a
consequence of the angle; it is the precondition that lets the angle exist at
all. This file imports `Analysis.CauchySchwarz` and feeds `cauchy_schwarz u v`
into `Real.cos_arccos` to discharge precisely that side condition — the
dependency is real rather than narrated.

The arrow therefore points one way only:

    cauchy_schwarz  ⟶  angle is well-defined  ⟶  ⟪u, v⟫ = ‖u‖ ‖v‖ cos θ

Running it backwards — using the angle to prove Cauchy–Schwarz — would be
circular, since the angle cannot be formed until the inequality is already in
hand. That is why `Analysis.CauchySchwarz` is careful to prove the bound with no
angles and no cosines.

## The unifying identity

With the angle in hand the cosine identity becomes a *theorem* rather than a
definition:

    ⟪u, v⟫ = ‖u‖ ‖v‖ cos (angle u v),

which is `inner_eq_norm_mul_norm_mul_cos_angle`. When `‖u‖ ‖v‖ ≠ 0` it is just
`cos (angle u v) = ⟪u, v⟫ / (‖u‖ ‖v‖)` — the content of `cos_angle` — multiplied
back through by the denominator. When `‖u‖ ‖v‖ = 0` one of the vectors is `0`,
both sides vanish, and the identity holds trivially. Pairing it with
`‖u‖ = √⟪u, u⟫` is the precise sense in which the inner product *is* Euclidean
geometry: length and angle both fall out of it, with Cauchy–Schwarz as the
gatekeeper that keeps the angle honest.

## The setting

We work over an arbitrary real inner-product space `F`:

  * `[SeminormedAddCommGroup F]` — vectors add, negate, and carry a *seminorm*
    `‖·‖` (a length not required to be definite);
  * `[InnerProductSpace ℝ F]` — there is a real inner product `⟪·,·⟫_ℝ`, tied to
    the seminorm by `⟪x, x⟫_ℝ = ‖x‖²`.

Both the well-definedness of the angle and the cosine identity rest only on
Cauchy–Schwarz, which holds over a seminorm; neither needs *definiteness*
(`‖x‖ = 0 → x = 0`), so this file stays at that weakest setting too. No dimension
or coordinate is mentioned either, so "angle" is defined in the plane, in `ℝⁿ`,
and in infinite-dimensional spaces alike.
-/

import Analysis.CauchySchwarz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Geometry

/-! We fix an arbitrary real inner-product space `F` for the whole file, the same
setting in which Cauchy–Schwarz was proved. -/
variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Length: read straight off the inner product

Nothing to prove. The norm of `u` is the square root of its self inner product —
the squared-norm bridge `⟪u, u⟫ = ‖u‖²` of the other files, taken back through a
square root. We exhibit the Mathlib lemma so the length half of the story has a
name on this page. -/

-- `‖u‖ = √⟪u, u⟫` — the norm *is* the inner product's square root.
example (u : F) : ‖u‖ = Real.sqrt ⟪u, u⟫_ℝ := norm_eq_sqrt_real_inner u

/-! ### Angle: defined, and well-defined only by Cauchy–Schwarz -/

/-- **The (unoriented) angle between two vectors**, defined as the arc-cosine of
the normalized inner product. This *is* the definition — there is no prior angle
it is proved equal to. If either vector is `0` the ratio is `0 / 0 = 0` and the
angle is `arccos 0 = π/2`, matching Mathlib's `InnerProductGeometry.angle`. The
whole content of the next lemma is that `arccos` is actually being handed a legal
input, which is where Cauchy–Schwarz earns its keep. -/
noncomputable def angle (u v : F) : ℝ :=
  Real.arccos (⟪u, v⟫_ℝ / (‖u‖ * ‖v‖))

/-- **Cosine of the angle.** `Real.cos` undoes the `arccos` in `angle`, leaving
the normalized inner product — *provided* that ratio lies in `[-1, 1]`. Proving
it does is the one place Cauchy–Schwarz is used, and the reason the angle is
well-defined at all. -/
theorem cos_angle (u v : F) :
    Real.cos (angle u v) = ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖) := by
  /- The argument to `arccos` is in range: its absolute value is at most `1`.
     Pull the absolute value through the quotient (`abs_div`, and `‖u‖‖v‖ ≥ 0`),
     then split on whether the denominator vanishes. If it does, the quotient is
     `_ / 0 = 0`, comfortably in range. If it does not, `div_le_one` reduces the
     claim to `|⟪u, v⟫| ≤ ‖u‖‖v‖` — which is exactly our `cauchy_schwarz`. -/
  have hbound : |⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)| ≤ 1 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ * ‖v‖)]
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ ‖u‖ * ‖v‖) with h | h
    · simp [← h]
    · rw [div_le_one h]
      exact Analysis.cauchy_schwarz u v
  /- `Real.cos_arccos` says `cos (arccos x) = x` exactly when `-1 ≤ x ≤ 1`. We
     unfold `angle` to expose the `arccos`, then feed it the two bounds extracted
     from `hbound` via `abs_le`. -/
  unfold angle
  exact Real.cos_arccos (abs_le.mp hbound).1 (abs_le.mp hbound).2

/-- **The dot-product–cosine identity**, `⟪u, v⟫ = ‖u‖ ‖v‖ cos θ`, now a theorem.
Together with `‖u‖ = √⟪u, u⟫` it shows the inner product determines both the
lengths and the angle of Euclidean geometry. -/
theorem inner_eq_norm_mul_norm_mul_cos_angle (u v : F) :
    ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ * Real.cos (angle u v) := by
  rcases eq_or_ne (‖u‖ * ‖v‖) 0 with h | h
  · /- Degenerate case `‖u‖‖v‖ = 0`. Over a *seminorm* this no longer forces `u`
       or `v` to be the zero vector, so we cannot route through `inner_zero_left`.
       We do not need to: Cauchy–Schwarz already bounds `|⟪u, v⟫|` by `‖u‖‖v‖`,
       which is `0` here, and a number whose absolute value is `≤ 0` must itself
       be `0`. Both sides of the identity then vanish. -/
    have hinner : ⟪u, v⟫_ℝ = 0 := by
      have hcs : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := Analysis.cauchy_schwarz u v
      rw [h] at hcs
      exact abs_eq_zero.mp (le_antisymm hcs (abs_nonneg _))
    rw [hinner, h, zero_mul]
  · /- Main case `‖u‖‖v‖ ≠ 0`: substitute `cos_angle` and cancel the denominator
       against the leading factor (`mul_div_cancel₀`). -/
    rw [cos_angle, mul_div_cancel₀ _ h]

end Geometry
