/-
# Pythagorean theorem

Our first real theorem: if vectors `u v` in a real inner-product space
are orthogonal (`⟨u, v⟩ = 0`), then `‖u + v‖² = ‖u‖² + ‖v‖²`.

This is the file where we stop *defining things* and start *proving math*.
Notice we no longer touch our own `Vec` type — we use mathlib's
`EuclideanSpace ℝ (Fin n)` directly. The whole inner-product machinery
(`⟪·,·⟫_ℝ`, `‖·‖`, bilinearity, symmetry) comes free.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

-- enables the `⟪x, y⟫_𝕜` notation for the inner product
open scoped InnerProductSpace

namespace Geometry

/-- **Pythagorean theorem**, proved from first principles.

The proof reads exactly like what you'd write on a blackboard:

    ‖u + v‖²
      = ⟨u + v, u + v⟩                       (defn. of norm-squared)
      = ⟨u, u + v⟩ + ⟨v, u + v⟩              (linearity in the 1st arg)
      = ⟨u,u⟩ + ⟨u,v⟩ + (⟨v,u⟩ + ⟨v,v⟩)      (linearity in the 2nd arg)
      = ‖u‖² + 0 + (0 + ‖v‖²)                (hypothesis + symmetry of ⟨·,·⟩_ℝ)
      = ‖u‖² + ‖v‖²                          (arithmetic)

`calc` lays the proof out as a chain of equalities. After each `_ =`
goes the next RHS; after `:=` goes the *justification* for that step.
The big lesson: in a good Lean proof, the text reads as the math. -/
theorem pythagoras {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (h : ⟪u, v⟫_ℝ = 0) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  calc ‖u + v‖ ^ 2
      = ⟪u + v, u + v⟫_ℝ                                       := by
          rw [real_inner_self_eq_norm_sq]
    _ = ⟪u, u + v⟫_ℝ + ⟪v, u + v⟫_ℝ                             := by
          rw [inner_add_left]
    _ = ⟪u, u⟫_ℝ + ⟪u, v⟫_ℝ + (⟪v, u⟫_ℝ + ⟪v, v⟫_ℝ)             := by
          rw [inner_add_right, inner_add_right]
    _ = ‖u‖ ^ 2 + ⟪u, v⟫_ℝ + (⟪v, u⟫_ℝ + ‖v‖ ^ 2)               := by
          rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v]
    _ = ‖u‖ ^ 2 + 0 + (0 + ‖v‖ ^ 2)                             := by
          rw [h, real_inner_comm u v, h]
    _ = ‖u‖ ^ 2 + ‖v‖ ^ 2                                       := by ring

/-- The same theorem, but using mathlib's prebuilt polarization identity
`‖x + y‖² = ‖x‖² + 2⟨x,y⟩ + ‖y‖²` (a.k.a. `norm_add_sq_real`).

Two lines. The entire expansion-and-cancellation dance from above lives
*inside* `norm_add_sq_real`, which has been proven once and for all for
any real inner-product space. This is what working with mathlib actually
feels like: most "proofs" become reductions to lemmas someone else proved
years ago. The from-scratch version above is what you write to
*understand* a theorem; this is what you write to *get on with your
life*. -/
theorem pythagoras' {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (h : ⟪u, v⟫_ℝ = 0) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring

end Geometry
