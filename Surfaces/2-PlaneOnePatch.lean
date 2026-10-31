import Surfaces.«0-Topology» /- isOpenSet_univ, isContinuous_of_lipschitz -/
import Surfaces.«0-Topology» /- isHomeomorphism_of_inverse -/
import Surfaces.«1-Surfaces» /- ℝ², ℝ³, SurfacePatch, IsSurface -/
import Mathlib.Algebra.BigOperators.Fin /- Fin.sum_univ_two -/
import Mathlib.Algebra.Group.Basic /- add_sub_cancel_left -/
import Mathlib.Algebra.Group.Defs /- add_assoc -/
import Mathlib.Algebra.Group.Monoid /- mul_one -/
import Mathlib.Algebra.Module.Defs /- sub_smul -/
import Mathlib.Algebra.Order.Group.Unbundled.Abs /- abs_nonneg -/
import Mathlib.Algebra.Order.Monoid.NatCast /- two_pos -/
import Mathlib.Algebra.Order.Ring.Abs /- sq_abs -/
import Mathlib.Analysis.InnerProductSpace.Basic /- inner_add_left, inner_smul_left -/
import Mathlib.Analysis.InnerProductSpace.Basic /- inner_sub_left, real_inner_comm, abs_real_inner_le_norm -/
import Mathlib.Analysis.InnerProductSpace.Defs /- ⟪x, p⟫ -/
import Mathlib.Analysis.InnerProductSpace.PiL2 /- !₂[s, t], EuclideanSpace.norm_eq -/
import Mathlib.Analysis.Normed.Group.Basic /- norm_add_le -/
import Mathlib.Analysis.Normed.Lp.PiLp /- PiLp.norm_apply_le -/
import Mathlib.Analysis.Normed.MulAction /- norm_smul -/
import Mathlib.Analysis.Real.Sqrt /- Real.sqrt_le_iff -/
import Mathlib.Data.Set.Defs /- {x | …}, Set.univ -/
import Mathlib.Data.Set.Operations /- Set.mem_univ -/
import Mathlib.Tactic.Abel /- abel -/
import Mathlib.Tactic.FinCases /- fin_cases -/
import Mathlib.Tactic.Linarith.Frontend /- linarith, nlinarith -/
import Mathlib.Tactic.Positivity.Core /- positivity -/

/-!
# A plane has an atlas with one patch

Pressley, *Elementary Differential Geometry*, 2nd ed., Example 4.1.2, pp. 68–69:

Every plane in `ℝ³` is a surface with an atlas consisting of a single surface patch.
In fact, let `a` be a point on the plane, and let `p` and `q` be two unit vectors that
are parallel to the plane and perpendicular to each other. If `v` is any point of
the plane, `v - a` is parallel to the plane, and so `v - a = u p + v q` for some scalars
`u` and `v`. Thus, the desired surface patch is `σ(u, v) = a + u p + v q`, and its
inverse map is `σ⁻¹(v) = ((v - a) · p, (v - a) · q)`. These formulas make it clear that
`σ` and `σ⁻¹` are continuous, and hence that `σ` is a homeomorphism.
-/

-- This enables `⟪v, p⟫` for the dot product `v · p`.
open scoped RealInnerProductSpace

/-- The plane through `a` spanned by `p` and `q` -/
def plane (a p q : ℝ³) : Set ℝ³ :=
  {x | ∃ u v : ℝ, x = a + u • p + v • q}

/-- `‖(s, t)‖ ≤ |s| + |t|` -/
theorem norm_le_abs_add_abs (s t : ℝ) :
    ‖!₂[s, t]‖ ≤ |s| + |t| := by
  rw [
    EuclideanSpace.norm_eq,
    Fin.sum_univ_two
  ]
  -- `s² + t² ≤ (|s| + |t|)²`
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp
    nlinarith [abs_nonneg s, abs_nonneg t, sq_abs s, sq_abs t]

namespace Plane

variable (a p q : ℝ³)

/-- `σ(u, v) = a + u p + v q` -/
def σ (x : ℝ²) : ℝ³ :=
  let u := x 0
  let v := x 1
  a + u • p + v • q

/-- `σ⁻¹(v) = ((v - a) · p, (v - a) · q)` -/
noncomputable def σInv (v : ℝ³) : ℝ² :=
  !₂[⟪v - a, p⟫, ⟪v - a, q⟫]

/-- `σ(u, v) = a + u p + v q` -/
theorem σ_apply (u v : ℝ) :
    σ a p q !₂[u, v] = a + u • p + v • q := by
  simp [σ]

section

variable {a p q}

-- `p` and `q` are perpendicular unit vectors.
variable (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ = 0)
include hp hq hpq

/-- `σ⁻¹(a + u p + v q) = (u, v)` -/
theorem σInv_apply (u v : ℝ) :
    σInv a p q (a + u • p + v • q) = !₂[u, v] := by
  -- `(a + u p + v q) - a = u p + v q`
  have h : a + u • p + v • q - a = u • p + v • q := by
    rw [
      add_assoc,
      add_sub_cancel_left
    ]
  rw [
    σInv,
    h
  ]
  simp [inner_add_left, inner_smul_left, real_inner_comm p q, hp, hq, hpq]

/-- `σ⁻¹(σ(x)) = x` -/
theorem σInv_σ (x : ℝ²) :
    σInv a p q (σ a p q x) = x := by
  rw [
    σ,
    σInv_apply hp hq hpq
  ]
  ext i
  fin_cases i <;> simp

/-- `σ(σ⁻¹(a + u p + v q)) = a + u p + v q` -/
theorem σ_σInv (u v : ℝ) :
    σ a p q (σInv a p q (a + u • p + v • q)) = a + u • p + v • q := by
  rw [
    σInv_apply hp hq hpq,
    σ_apply
  ]

-- Only `‖p‖ = ‖q‖ = 1` is needed here.
omit hpq in
/-- `‖σ(x) - σ(y)‖ ≤ 2 ‖x - y‖` -/
theorem norm_σ_sub_le (x y : ℝ²) :
    ‖σ a p q x - σ a p q y‖ ≤ 2 * ‖x - y‖ := by
  -- `σ(x) - σ(y) = (x₀ - y₀) p + (x₁ - y₁) q`
  have h : σ a p q x - σ a p q y = (x 0 - y 0) • p + (x 1 - y 1) • q := by
    simp only [σ, sub_smul]
    abel
  -- `|x₀ - y₀|` and `|x₁ - y₁|` are at most `‖x - y‖`
  have h0 : ‖x 0 - y 0‖ ≤ ‖x - y‖ := by
    simpa using PiLp.norm_apply_le (x - y) 0
  have h1 : ‖x 1 - y 1‖ ≤ ‖x - y‖ := by
    simpa using PiLp.norm_apply_le (x - y) 1
  rw [h]
  calc ‖(x 0 - y 0) • p + (x 1 - y 1) • q‖
      ≤ ‖(x 0 - y 0) • p‖ + ‖(x 1 - y 1) • q‖ := norm_add_le _ _
    _ = ‖x 0 - y 0‖ + ‖x 1 - y 1‖ := by
      rw [
        norm_smul,
        norm_smul,
        hp,
        hq,
        mul_one,
        mul_one
      ]
    _ ≤ 2 * ‖x - y‖ := by linarith

-- Only `‖p‖ = ‖q‖ = 1` is needed here.
omit hpq in
/-- `‖σ⁻¹(x) - σ⁻¹(y)‖ ≤ 2 ‖x - y‖` -/
theorem norm_σInv_sub_le (x y : ℝ³) :
    ‖σInv a p q x - σInv a p q y‖ ≤ 2 * ‖x - y‖ := by
  -- `σ⁻¹(x) - σ⁻¹(y) = ((x - y) · p, (x - y) · q)`
  have h : σInv a p q x - σInv a p q y = !₂[⟪x - y, p⟫, ⟪x - y, q⟫] := by
    ext i
    fin_cases i <;> simp [σInv, inner_sub_left]
  -- Cauchy–Schwarz: `|(x - y) · p| ≤ ‖x - y‖ ‖p‖ = ‖x - y‖`
  have hp' : |⟪x - y, p⟫| ≤ ‖x - y‖ := by
    simpa [hp] using abs_real_inner_le_norm (x - y) p
  have hq' : |⟪x - y, q⟫| ≤ ‖x - y‖ := by
    simpa [hq] using abs_real_inner_le_norm (x - y) q
  rw [h]
  calc ‖!₂[⟪x - y, p⟫, ⟪x - y, q⟫]‖
      ≤ |⟪x - y, p⟫| + |⟪x - y, q⟫| := norm_le_abs_add_abs _ _
    _ ≤ 2 * ‖x - y‖ := by linarith

/-- `σ : ℝ² → plane` is a surface patch with `U = ℝ²` and `W = ℝ³` -/
noncomputable def patch : SurfacePatch (plane a p q) where
  toFun := σ a p q
  U := Set.univ
  W := Set.univ
  isOpen_U := isOpenSet_univ
  isOpen_W := isOpenSet_univ
  isHomeomorphism :=
    isHomeomorphism_of_inverse (σInv a p q)
      (mapsTo_f := fun x _ => ⟨⟨x 0, x 1, rfl⟩, Set.mem_univ _⟩)
      (mapsTo_fInv := fun _ _ => Set.mem_univ _)
      (fInv_f := fun x _ => σInv_σ hp hq hpq x)
      (f_fInv := by
        rintro _ ⟨⟨u, v, rfl⟩, -⟩
        exact σ_σInv hp hq hpq u v)
      (continuous_f := isContinuous_of_lipschitz two_pos
        (fun x _ y _ => norm_σ_sub_le hp hq x y))
      (continuous_fInv := isContinuous_of_lipschitz two_pos
        (fun x _ y _ => norm_σInv_sub_le hp hq x y))

end

end Plane

/-- The plane through `a` spanned by perpendicular unit vectors `p` and `q` is a surface -/
theorem plane_isSurface
    {a p q : ℝ³}
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1)
    (hpq : ⟪p, q⟫ = 0) :
    IsSurface (plane a p q) :=
  fun _ _ =>
    ⟨Plane.patch hp hq hpq, Set.mem_univ _⟩
