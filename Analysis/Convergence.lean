/-
# Convergence, Cauchy sequences, and completeness

The inner-product results in these libraries so far are *finite* algebra. The
Pythagorean theorem, the parallelogram law, and the triangle inequality over in
`Geometry`, and Cauchy–Schwarz here beside this file in `Analysis` — each expands
a squared norm of one or two vectors, pushes it through bilinearity, and stops.
Hilbert spaces ask a question those tools cannot answer: when does an *infinite*
sequence of vectors `u₀, u₁, u₂, …` settle down onto a limit? A Hilbert space is
an inner-product space in which the answer is always "whenever it should" —
every sequence that *ought* to converge actually does. Pinning down "ought to"
and "does" is the job of this file.

Like `Bilinearity.lean`, this file is built mostly from `example`s: it names the
Mathlib machinery of convergence and exhibits each piece, discharged by the real
lemma, so every idea is introduced and made concrete before anything leans on it.
It defines nothing and proves nothing geometric. But unlike `Bilinearity.lean` it
is not inert — it **exports exactly one theorem**, `exists_limit_of_cauchySeq`:
the fact that in a complete space a Cauchy sequence has a limit. That single
lemma is the analytic foundation the whole Hilbert-space story rests on, and
exporting it by name lets the `Geometry` files `import Analysis.Convergence` and
*call* it, so the dependency running down from geometry into analysis is real
rather than narrated — the standard the rest of the repo holds itself to.
Everything else here stays an unexported `example`. And — the surprise — *the
inner product never appears in this file*. Not even the norm appears until the
very last line: convergence is a coarser idea than either, and saying exactly how
coarse is half the point. (Naming the one fact geometry borrows is the other.)

## One idea, five floors

"A sequence converges" is not a single notion living at a single level of
structure. It splits into a stack of weaker and weaker statements, each at home
in a weaker and weaker kind of space. Maximizing generality means stating each
piece exactly where it is born, and not one floor higher:

  * **Convergence — `uₙ → a` — is topological.** To say the terms eventually
    enter every neighbourhood of `a`, all you need is a notion of
    "neighbourhood": a `TopologicalSpace`. No distance, no arithmetic.
  * **Cauchy and completeness are uniform.** "The terms get close *to each
    other*" compares two points without reference to any limit, and that
    comparison needs a `UniformSpace` — a structure of "closeness of pairs" —
    but still no numbers.
  * **The ε–N descriptions are metric.** The familiar `∀ ε > 0, ∃ N, …` only
    means something once "close" is measured by a real number, i.e. in a
    `PseudoMetricSpace`. This is the floor beneath which ε cannot go: an ε *is*
    a distance.
  * **Unique limits are about separation.** That a sequence cannot converge to
    two different points is the Hausdorff (`T2Space`) property — nothing to do
    with distance. A genuine metric happens to be `T2`; a pseudometric does not.
  * **The norm is just one source of a metric.** Only at the end does a norm
    reappear, via `dist x y = ‖x - y‖`, and through it the whole stack lands on
    the inner-product spaces the `Geometry` files work over.

## Design note: how general, and why

An earlier draft fixed a single setting `[MetricSpace X]` for the entire file.
We rejected it: it is *true* but not *honest*. Stating Cauchyness or
completeness over a metric space demands far more structure (a real-valued
distance) than either notion uses (a uniformity), and it hides that convergence
itself needs nothing but a topology. The file you are reading instead **ascends
the hierarchy** `TopologicalSpace → UniformSpace → PseudoMetricSpace → T2Space →
SeminormedAddCommGroup`, declaring in each section the weakest structure its results
require — exactly the discipline these files already apply when they phrase a
theorem over an abstract inner-product space rather than over `ℝⁿ`. The payoff
is that the file *shows*, rather than asserts, where each idea lives: the
typeclass on each `example` is a machine-checked claim that the result needs no
more than that. Generality bottoms out in precisely two places, and the file
marks both — ε needs a metric, uniqueness needs separation.

One more choice is recorded here. The file otherwise exports nothing, in the
manner of `Bilinearity.lean` — but it *does* export the single completeness
bridge `exists_limit_of_cauchySeq`. The alternative was to leave even that an
unexported `example` and have the projection theorem call Mathlib's
`cauchySeq_tendsto_of_complete` directly, narrating the link back to this lesson.
We export the named version instead, so the cross-library edge `Geometry →
Analysis` is a real `import`-and-call — exactly as `Geometry.TriangleInequality`
calls our `cauchy_schwarz` rather than Mathlib's. Dependency real, not narrated.

## The setting

There is deliberately no single `variable` block. Each section opens with the
weakest structure that supports it, and sequences are indexed by `ℕ` throughout
(`ℕ` supplies the `Nonempty` and `SemilatticeSup` instances the sequence lemmas
ask of the index). The `open`s below bring the filter `atTop` ("eventually, for
large `n`") and the neighbourhood-filter notation `𝓝`.
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Cauchy

open Filter
open scoped Topology

namespace Analysis.Convergence

/-! ### Floor 1 — convergence is topological

`uₙ → a` is written `Tendsto u atTop (𝓝 a)`: along the filter `atTop` of large
indices, the terms eventually lie in every neighbourhood `𝓝 a` of the limit. The
only structure this mentions is the neighbourhood filter, so it is well-formed in
any `TopologicalSpace`. The `example` below carries *only* `[TopologicalSpace X]`;
that it elaborates at all is the proof of the claim. -/

section Topological
variable {X : Type*} [TopologicalSpace X]

-- Convergence of a sequence to a limit, as a `Prop`, needing only a topology.
example (u : ℕ → X) (a : X) : Prop := Tendsto u atTop (𝓝 a)

end Topological

/-! ### Floor 2 — Cauchy and completeness are uniform

A sequence is **Cauchy** when its terms grow close *to one another* — a statement
about pairs of terms that never names a limit. Comparing two points for
closeness without a metric is exactly what a `UniformSpace` provides, so
`CauchySeq` lives here, one floor below any distance. -/

section Uniform
variable {X : Type*} [UniformSpace X]

-- The Cauchy condition, as a `Prop`, needing only a uniformity.
example (u : ℕ → X) : Prop := CauchySeq u

/-! The two directions relating convergence and Cauchyness are *not* symmetric,
and that asymmetry is the entire content of "completeness".

The easy direction always holds: a sequence that closes in on a limit must close
in on itself (if every late term is within `ε/2` of `a`, any two of them are
within `ε` of each other). Mathlib packages this as `Filter.Tendsto.cauchySeq`. -/

-- Convergent ⟹ Cauchy — always true, no completeness required.
example (u : ℕ → X) (a : X) (h : Tendsto u atTop (𝓝 a)) : CauchySeq u :=
  h.cauchySeq

/-! The converse — Cauchy ⟹ convergent — is *false* in general. In `ℚ` the
truncations of `√2` huddle arbitrarily close together yet converge to no rational
number: the limit they reach for has been deleted from the space. A space where
this can never happen — where every Cauchy sequence does reach a genuine limit —
is called **complete**, and Mathlib records the property as the class
`CompleteSpace`. It is not a theorem but a *hypothesis*: precisely the missing
axiom that closes the gap. Granted it, a Cauchy sequence does reach a limit — and
recording that bridge is the one job this file does beyond exhibiting: we export
it as the named theorem `exists_limit_of_cauchySeq` (Mathlib's
`cauchySeq_tendsto_of_complete` under our own roof) so the projection theorem can
call it by name. -/

/-- **Completeness delivers limits.** In a complete space every Cauchy sequence
converges — it has a genuine limit. This is the file's lone export: the bridge a
Cauchy minimizing sequence crosses to become an actual closest point in the
Hilbert projection theorem. It is `cauchySeq_tendsto_of_complete` under our own
roof, stated over the weakest setting that carries it — a `UniformSpace` that is
`CompleteSpace` — so the `Geometry` files can `import Analysis.Convergence` and
call it by name. -/
theorem exists_limit_of_cauchySeq [CompleteSpace X] {u : ℕ → X}
    (h : CauchySeq u) : ∃ a, Tendsto u atTop (𝓝 a) :=
  cauchySeq_tendsto_of_complete h

end Uniform

/-! ### Floor 3 — the ε–N descriptions are metric

Everything above was said without a single real number. The textbook
`∀ ε > 0, ∃ N, …` characterisations live one floor up, in a `PseudoMetricSpace`,
because they measure "close" with a distance `dist`. These are the human-readable
faces of the two filter definitions; `Metric.tendsto_atTop` and
`Metric.cauchySeq_iff` certify that the faces and the definitions agree. This is
the floor beneath which generality cannot pass: an ε is a distance, so it cannot
exist below a metric. -/

section Pseudometric
variable {X : Type*} [PseudoMetricSpace X]

-- ε–N face of convergence: eventually within ε of the limit.
example (u : ℕ → X) (a : X) :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

-- ε–N face of Cauchy: eventually all terms within ε of each other.
example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

end Pseudometric

/-! ### Floor 4 — unique limits are about separation

Can a sequence converge to two different points at once? In general, yes — but
not if distinct points can be separated by disjoint neighbourhoods, the
**Hausdorff** (`T2Space`) property. So uniqueness of limits is not a metric fact
at all; its weakest home is `[T2Space X]`, and `tendsto_nhds_unique` proves it
there. The link back to distance is a single implication: a genuine `MetricSpace`
is `T2` (its definiteness, `dist x y = 0 → x = y`, separates points), whereas a
*pseudo*metric is not — drop definiteness and two points at distance `0` are both
limits of the constant sequence. That is the exact metric shadow of the inner
product's own definiteness `⟪x, x⟫ = 0 → x = 0`. -/

section Hausdorff
variable {X : Type*} [TopologicalSpace X] [T2Space X]

-- A sequence has at most one limit — a separation fact, not a metric one.
example (u : ℕ → X) (a b : X)
    (ha : Tendsto u atTop (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

end Hausdorff

/-! ### Floor 5 — the norm supplies a metric

Nothing above mentioned a norm; convergence never needed one. A norm enters only
now, as *one source* of a distance: in any `SeminormedAddCommGroup` the distance is
`dist x y = ‖x - y‖` (`dist_eq_norm`). This is the single rung joining the whole
stack to the inner-product spaces of these libraries — and it lands them at
exactly this floor, because a real inner-product space *is* a
`SeminormedAddCommGroup`: that is the weakest group `InnerProductSpace` is declared
over, and the setting the `Geometry` files work in. Instantiating `X := F`
therefore drops convergence, Cauchyness, and completeness straight onto our
vectors. *Uniqueness* of limits is the one piece that asks for more: it needs the
`T2Space` of Floor 4, which a seminorm does not supply — two vectors at distance
`0` would share every limit. That separation arrives only with *definiteness*
(`‖x‖ = 0 → x = 0`), the upgrade from `SeminormedAddCommGroup` to
`NormedAddCommGroup`, and it is the very inner-product definiteness whose metric
shadow Floor 4 named. A **Hilbert space** is then exactly an inner-product space
`F` carrying `[CompleteSpace F]`; the projection theorem will build a Cauchy
sequence with the parallelogram law and call this file's `exists_limit_of_cauchySeq`
to hand it the limit completeness guarantees. -/

section Normed
variable {F : Type*} [SeminormedAddCommGroup F]

-- The norm induces the metric: the only bridge back to our world.
example (a b : F) : dist a b = ‖a - b‖ := dist_eq_norm a b

end Normed

end Analysis.Convergence
