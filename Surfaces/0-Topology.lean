import Mathlib.Algebra.Group.Basic /- add_sub_cancel_left -/
import Mathlib.Algebra.Group.Monoid /- mul_one -/
import Mathlib.Algebra.Group.Semigroup /- add_assoc -/
import Mathlib.Algebra.GroupWithZero.Units.Basic /- mul_div_cancel₀ -/
import Mathlib.Algebra.Module.Defs /- add_smul -/
import Mathlib.Algebra.Order.Field.Basic /- half_pos, half_lt_self -/
import Mathlib.Algebra.Order.Group.Unbundled.Abs /- abs_of_pos -/
import Mathlib.Algebra.Order.Group.Unbundled.Basic /- sub_pos -/
import Mathlib.Algebra.Order.GroupWithZero.Basic /- div_pos -/
import Mathlib.Algebra.Order.GroupWithZero.Defs /- mul_lt_mul_of_pos_left -/
import Mathlib.Algebra.Order.ZeroLEOne /- one_pos -/
import Mathlib.Analysis.InnerProductSpace.PiL2 /- EuclideanSpace, EuclideanSpace.single -/
import Mathlib.Analysis.Normed.Group.Basic /- norm_sub_le_norm_sub_add_norm_sub -/
import Mathlib.Analysis.Normed.Group.Defs /- NormedAddCommGroup, ‖u‖ -/
import Mathlib.Analysis.Normed.Group.Real /- Real.norm_eq_abs -/
import Mathlib.Analysis.Normed.MulAction /- norm_smul -/
import Mathlib.Basic.Real.Basic /- ℝ -/
import Mathlib.Data.Set.Defs /- {u | …}, Set.univ -/
import Mathlib.Data.Set.Function /- Set.InvOn.bijOn -/
import Mathlib.Data.Set.Operations /- Set.MapsTo, Set.BijOn, Set.InvOn, Set.mem_univ -/
import Mathlib.Tactic.Linarith.Frontend /- linarith -/

/-!
# Topology

A surface is a subset of `ℝ³` that looks like a piece of the plane near each of its points.
Making "looks like" and "near" precise needs three ideas, which this file builds from scratch
using nothing but the distance `‖u - a‖` between points:

* *open sets*, the sets in which every point has some room around it;
* *continuous maps*, which send nearby points to nearby points;
* *homeomorphisms*, continuous bijections with continuous inverses, which identify two sets
  as the same shape.

Pressley, *Elementary Differential Geometry*, 2nd ed., Section 4.1, pp. 67–68:

To make the phrases 'looks like' and 'in the vicinity' precise, we must first introduce some
preliminary material. We describe this for `ℝᴺ` for any `N ≥ 1`, although we shall need it only
for `N = 1`, `2`, or `3`.
-/

-- `M` and `N` are dimensions. Lean adds them as implicit arguments wherever they are used.
variable {M N : ℕ}

/-- `ℝᴹ`, Euclidean space of dimension `M`. See `ℝᴺ`. -/
local notation "ℝᴹ" => EuclideanSpace ℝ (Fin M)

/-- `ℝᴺ`, Euclidean space of dimension `N`: points are `N`-tuples of real numbers, and the
distance between two points is `‖u - a‖ = √((u₁ - a₁)² + ⋯ + (u_N - a_N)²)`.

Mathlib calls this space `EuclideanSpace ℝ (Fin N)`. Its points are functions from the index set
`Fin N = {0, 1, …, N - 1}` to `ℝ`, and `‖·‖` is the Euclidean norm. -/
local notation "ℝᴺ" => EuclideanSpace ℝ (Fin N)

/-- **Open sets.** A set `U ⊆ ℝᴺ` is *open* when every point of `U` has some room around
it: for each `a ∈ U` there is a radius `ε > 0` such that the whole ball of radius `ε` about `a`
stays inside `U`. For example, the disc `x² + y² < 1` is open. The disc `x² + y² ≤ 1` is not,
because a point on the circle has points just outside the disc arbitrarily close to it.

In Lean, `IsOpenSet U` is a proposition, a statement that is either true or false. It says: for
every `a ∈ U` there exists `ε > 0` such that every `u` with `‖u - a‖ < ε` is in `U`.

Pressley: "a subset `U` of `ℝᴺ` is called *open* if, whenever `a` is a point in `U`, there is a
positive number `ε` such that every point `u ∈ ℝᴺ` within a distance `ε` of `a` is also in `U`." -/
def IsOpenSet (U : Set ℝᴺ) : Prop :=
  ∀ a ∈ U, ∃ ε > 0, ∀ u, ‖u - a‖ < ε → u ∈ U

/-- **Open balls.** `Dᵣ(a)` is the set of points at distance *less than* `r` from the centre `a`.
In `ℝ¹` it is an open interval, in `ℝ²` an open disc, and in `ℝ³` a solid ball without its
boundary sphere. Open balls are the basic examples of open sets: the definition of an open set
says that every point of the set is the centre of an open ball inside it.

Notation: the `D` stands for *disc*, the picture in `ℝ²`; many books write `B` for *ball*
instead. The subscript `r` is the radius and `(a)` is the centre, so `D₁(0)` is the open ball of
radius `1` about the origin.

In Lean, `openBall a r` is a set, written in set-builder notation `{u | ‖u - a‖ < r}`. -/
def openBall (a : ℝᴺ) (r : ℝ) : Set ℝᴺ :=
  {u | ‖u - a‖ < r}

/-- **Closed balls.** `D̄ᵣ(a)` is the set of points at distance *at most* `r` from the centre `a`.
Unlike the open ball `Dᵣ(a)`, it contains its boundary sphere `‖u - a‖ = r`, and that is exactly
why it fails to be open (`not_isOpenSet_closedBall`).

Notation: a bar over a set denotes its *closure*, the set together with all the points it gets
arbitrarily close to. The points that `Dᵣ(a)` gets arbitrarily close to without containing are
those on its boundary sphere, so its closure `D̄ᵣ(a)` is the open ball plus that sphere.

In Lean, `closedBall a r` is the set `{u | ‖u - a‖ ≤ r}`. -/
def closedBall (a : ℝᴺ) (r : ℝ) : Set ℝᴺ :=
  {u | ‖u - a‖ ≤ r}

/-- **The whole space is open.** Every point of `ℝᴺ` trivially has room around it, because
there is nothing outside `ℝᴺ` to bump into. Any radius works, and the proof takes `ε = 1`.

The plane in `2-PlaneOnePatch` uses this: its single patch is defined on all of `ℝ²`, and the
open set `W` cutting out the plane is all of `ℝ³`. -/
theorem isOpenSet_univ : IsOpenSet (Set.univ : Set ℝᴺ) := by
  intro a _
  exact ⟨1, one_pos, fun u _ => Set.mem_univ u⟩

/-- **Open balls are open.** If `b` is in `Dᵣ(a)`, then `b` is at distance `‖b - a‖ < r` from
the centre, leaving a margin of `r - ‖b - a‖` before the edge. The ball of that radius about `b`
fits inside `Dᵣ(a)`, by the triangle inequality `‖u - a‖ ≤ ‖u - b‖ + ‖b - a‖`.

This justifies the name: the open ball really is an open set. -/
theorem isOpenSet_openBall (a : ℝᴺ) (r : ℝ) : IsOpenSet (openBall a r) := by
  intro b b_in_ball
  refine ⟨r - ‖b - a‖, sub_pos.mpr b_in_ball, fun u u_near_b => ?_⟩
  -- Triangle inequality: `‖u - a‖ ≤ ‖u - b‖ + ‖b - a‖ < r`
  have triangle := norm_sub_le_norm_sub_add_norm_sub u b a
  change ‖u - a‖ < r
  linarith

/-- **Closed balls are not open.** The point `a + r e = (a₁ + r, a₂, …, a_N)` lies on the
boundary sphere of `D̄ᵣ(a)`. However small a radius `ε` we try around it, the point
`(a₁ + r + ε/2, a₂, …, a_N)` is within `ε` of it but at distance `r + ε/2 > r` from `a`,
so it lies outside `D̄ᵣ(a)`. No radius works, so `D̄ᵣ(a)` is not open.

In Lean, `¬IsOpenSet (closedBall a r)` means "assuming `D̄ᵣ(a)` is open leads to a
contradiction". The hypothesis `1 ≤ N` guarantees there is a first coordinate to move along. -/
theorem not_isOpenSet_closedBall
    (N_pos : 1 ≤ N)
    (a : ℝᴺ)
    {r : ℝ}
    (r_pos : 0 < r) :
    ¬IsOpenSet (closedBall a r) := by
  -- `e = (1, 0, …, 0)`, so `a + r e = (a₁ + r, a₂, …, a_N)`.
  obtain ⟨e, e_unit⟩ : ∃ e : ℝᴺ, ‖e‖ = 1 :=
    ⟨EuclideanSpace.single ⟨0, N_pos⟩ 1, by simp⟩
  intro closedBall_open
  -- `a + r e ∈ D̄ᵣ(a)`
  have boundary_in_ball : a + r • e ∈ closedBall a r := by
    simp [closedBall, norm_smul, e_unit, abs_of_pos r_pos]
  obtain ⟨ε, ε_pos, near_in_ball⟩ := closedBall_open (a + r • e) boundary_in_ball
  -- `a + (r + ε/2) e` is within `ε` of `a + r e`
  have near : ‖(a + (r + ε / 2) • e) - (a + r • e)‖ < ε := by
    rw [
      add_smul,
      ← add_assoc,
      add_sub_cancel_left,
      norm_smul,
      e_unit,
      mul_one,
      Real.norm_eq_abs,
      abs_of_pos (half_pos ε_pos)
    ]
    exact half_lt_self ε_pos
  -- so `a + (r + ε/2) e ∈ D̄ᵣ(a)`, which says `r + ε/2 ≤ r`
  have far_in_ball : ‖(a + (r + ε / 2) • e) - a‖ ≤ r := near_in_ball _ near
  rw [
    add_sub_cancel_left,
    norm_smul,
    e_unit,
    mul_one,
    Real.norm_eq_abs,
    abs_of_pos (by linarith)
  ] at far_in_ball
  linarith

/-- **Continuity at a point.** A map `f : X → Y` is continuous at `a ∈ X` when points of `X`
near `a` are sent to points near `f(a)`. Precisely: however small a tolerance `ε > 0` we demand
on the output, there is a `δ > 0` such that every `u ∈ X` within `δ` of `a` has `f(u)` within `ε`
of `f(a)`. Think of `ε` as a challenge and `δ` as the response.

In Lean, a map `f : X → Y` between subsets `X ⊆ ℝᴹ` and `Y ⊆ ℝᴺ` is written as a function
`f : ℝᴹ → ℝᴺ` together with the set `X`. Only the points `u ∈ X` are ever tested, so the values
of `f` outside `X` do not matter. -/
def IsContinuousAt (f : ℝᴹ → ℝᴺ) (X : Set ℝᴹ) (a : ℝᴹ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ u ∈ X, ‖u - a‖ < δ → ‖f u - f a‖ < ε

/-- **Continuous maps.** `f` is continuous on `X` when it is continuous at every point of `X`.
Informally, `f` does not tear: it never sends points that are close together in `X` to points
that are far apart.

Surface patches are continuous maps from an open set in `ℝ²` onto a piece of a surface. -/
def IsContinuous (f : ℝᴹ → ℝᴺ) (X : Set ℝᴹ) : Prop :=
  ∀ a ∈ X, IsContinuousAt f X a

/-- **Continuity in terms of open sets.** `f` is continuous on `X` exactly when, for every
open set `V`, the points of `X` that `f` sends into `V` are the points of `X` that lie in some
open set `U`, i.e. `U ∩ X = {x ∈ X | f(x) ∈ V}`. In short: preimages of open sets are open
(relative to `X`).

This version mentions no `ε` or `δ`, only open sets, and it is how continuity is defined in
general topology. The proof translates between the two: an `ε`-ball in `V` corresponds to a
`δ`-ball in `U`. -/
theorem isContinuous_iff_isOpenSet {f : ℝᴹ → ℝᴺ} {X : Set ℝᴹ} :
    IsContinuous f X ↔
      ∀ V, IsOpenSet V → ∃ U, IsOpenSet U ∧ U ∩ X = {x ∈ X | f x ∈ V} := by
  constructor
  · intro continuous_f V V_open
    -- `U` is the union of the balls `D_δ(a)`, `a ∈ X`, whose points in `X` are mapped into `V`.
    refine ⟨{u | ∃ a ∈ X, ∃ δ > 0, (∀ x ∈ X, ‖x - a‖ < δ → f x ∈ V) ∧ ‖u - a‖ < δ}, ?_, ?_⟩
    · -- `U` is open because each `D_δ(a)` is.
      rintro u ⟨a, a_in_X, δ, δ_pos, ball_into_V, u_near_a⟩
      refine ⟨δ - ‖u - a‖, sub_pos.mpr u_near_a, fun w w_near_u => ?_⟩
      have triangle := norm_sub_le_norm_sub_add_norm_sub w u a
      exact ⟨a, a_in_X, δ, δ_pos, ball_into_V, by linarith⟩
    · ext x
      constructor
      · rintro ⟨⟨a, a_in_X, δ, δ_pos, ball_into_V, x_near_a⟩, x_in_X⟩
        exact ⟨x_in_X, ball_into_V x x_in_X x_near_a⟩
      · rintro ⟨x_in_X, fx_in_V⟩
        -- `V` contains a ball around `f(x)`, and continuity pulls it back to a ball around `x`.
        obtain ⟨ε, ε_pos, ball_in_V⟩ := V_open (f x) fx_in_V
        obtain ⟨δ, δ_pos, f_close⟩ := continuous_f x x_in_X ε ε_pos
        have ball_into_V : ∀ y ∈ X, ‖y - x‖ < δ → f y ∈ V :=
          fun y y_in_X y_near_x => ball_in_V (f y) (f_close y y_in_X y_near_x)
        exact ⟨⟨x, x_in_X, δ, δ_pos, ball_into_V, by simpa using δ_pos⟩, x_in_X⟩
  · intro open_preimages a a_in_X ε ε_pos
    -- Pull back the open ball `D_ε(f(a))` to an open `U ∋ a`, which contains a ball `D_δ(a)`.
    obtain ⟨U, U_open, U_inter_X⟩ := open_preimages (openBall (f a) ε) (isOpenSet_openBall _ _)
    have a_in_U : a ∈ U ∩ X := by
      rw [U_inter_X]
      exact ⟨a_in_X, show ‖f a - f a‖ < ε by simpa using ε_pos⟩
    obtain ⟨δ, δ_pos, ball_in_U⟩ := U_open a a_in_U.1
    refine ⟨δ, δ_pos, fun u u_in_X u_near_a => ?_⟩
    have u_in_U : u ∈ U ∩ X := ⟨ball_in_U u u_near_a, u_in_X⟩
    rw [U_inter_X] at u_in_U
    exact u_in_U.2

/-- **Homeomorphisms.** `f : X → Y` is a *homeomorphism* when it is continuous, bijective, and
its inverse `f⁻¹ : Y → X` is continuous too. Then `X` and `Y` are *homeomorphic*: `f` matches
their points one to one, and nearness in `X` corresponds exactly to nearness in `Y`. A coffee mug
and a doughnut are homeomorphic, while a sphere and a plane are not.

A surface patch is a homeomorphism from an open set `U ⊆ ℝ²` onto a piece `S ∩ W` of the
surface. This is what "the surface looks like a piece of the plane" means.

In Lean, `Set.BijOn f X Y` says `f` is a bijection from `X` onto `Y`, and `Set.InvOn fInv f X Y`
says `fInv` undoes `f` in both directions. -/
def IsHomeomorphism (f : ℝᴹ → ℝᴺ) (X : Set ℝᴹ) (Y : Set ℝᴺ) : Prop :=
  IsContinuous f X ∧
    Set.BijOn f X Y ∧
      ∃ fInv : ℝᴺ → ℝᴹ, Set.InvOn fInv f X Y ∧ IsContinuous fInv Y

/-- **Proving a map is a homeomorphism.** The practical recipe: write down a candidate inverse
`f⁻¹`, then check that

* `f` maps `X` into `Y`, and `f⁻¹` maps `Y` into `X`;
* `f⁻¹(f(x)) = x` for `x ∈ X`, and `f(f⁻¹(y)) = y` for `y ∈ Y`;
* `f` and `f⁻¹` are both continuous.

Bijectivity then comes for free. Each surface patch in Pressley's examples is shown to be a
homeomorphism this way. -/
theorem isHomeomorphism_of_inverse
    {f : ℝᴹ → ℝᴺ}
    {X : Set ℝᴹ}
    {Y : Set ℝᴺ}
    (fInv : ℝᴺ → ℝᴹ)
    (mapsTo_f : Set.MapsTo f X Y)
    (mapsTo_fInv : Set.MapsTo fInv Y X)
    (fInv_f : Set.LeftInvOn fInv f X)
    (f_fInv : Set.RightInvOn fInv f Y)
    (continuous_f : IsContinuous f X)
    (continuous_fInv : IsContinuous fInv Y) :
    IsHomeomorphism f X Y :=
  ⟨continuous_f,
    Set.InvOn.bijOn ⟨fInv_f, f_fInv⟩ mapsTo_f mapsTo_fInv,
    fInv,
    ⟨fInv_f, f_fInv⟩,
    continuous_fInv⟩

/-- **Maps that stretch distances by a bounded factor are continuous.** If there is a constant
`C > 0` with `‖f(u) - f(a)‖ ≤ C ‖u - a‖` for all `u` and `a` in `X`, then `f` is continuous: to get
`f(u)` within `ε` of `f(a)`, take `u` within `δ = ε / C` of `a`. Such maps are called
*Lipschitz*.

Linear and affine maps are Lipschitz, which is how the plane's patch `σ(u, v) = a + u p + v q`
and its inverse are shown to be continuous. -/
theorem isContinuous_of_lipschitz
    {f : ℝᴹ → ℝᴺ}
    {X : Set ℝᴹ}
    {C : ℝ}
    (C_pos : 0 < C)
    (stretch_le : ∀ u ∈ X, ∀ a ∈ X, ‖f u - f a‖ ≤ C * ‖u - a‖) :
    IsContinuous f X := by
  intro a a_in_X ε ε_pos
  refine ⟨ε / C, div_pos ε_pos C_pos, fun u u_in_X u_near_a => ?_⟩
  calc ‖f u - f a‖
      ≤ C * ‖u - a‖ := stretch_le u u_in_X a a_in_X
    _ < C * (ε / C) := mul_lt_mul_of_pos_left u_near_a C_pos
    _ = ε := mul_div_cancel₀ ε C_pos.ne'
