import Surfaces.«3-Curvature» /- K -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic /- Matrix.det -/
import Mathlib.LinearAlgebra.Matrix.Notation /- !![a, b, c; d, e, f; g, h, i] -/
import Mathlib.Topology.MetricSpace.Pseudo.Defs /- Metric.sphere -/

/-!
# 4. Theorema Egregium

Gaussian curvature is defined from the second fundamental form, which depends on how the surface
sits in `ℝ³`. Gauss's *remarkable theorem* says that `K` depends only on the first fundamental
form, that is, on lengths measured within the surface (Pressley, Theorem 10.2.1). The Brioschi
formula expresses `K` in terms of `E`, `F`, `G`, and their derivatives (Corollary 10.2.2).

The cylinder of `3-Curvature` is flat for this reason. Unrolling it onto the plane preserves
lengths, so it has the plane's curvature, `K = 0`.
-/

open Patch

/-- **The Brioschi formula** (Pressley, Corollary 10.2.2). `K (EG - F²)² = det A - det B`, where the
entries of `A` and `B` are built from `E`, `F`, `G`, and their first and second derivatives. -/
theorem K_eq_brioschi {S : Set ℝ³} (σ : AllowablePatch S) {q : ℝ²} (hq : q ∈ σ.U) :
    let E := E σ.toFun
    let F := F σ.toFun
    let G := G σ.toFun
    K σ.toFun q =
      (Matrix.det !![-(1 / 2) * ∂ᵥ (∂ᵥ E) q + ∂ᵥ (∂ᵤ F) q - (1 / 2) * ∂ᵤ (∂ᵤ G) q,
            (1 / 2) * ∂ᵤ E q, ∂ᵤ F q - (1 / 2) * ∂ᵥ E q;
          ∂ᵥ F q - (1 / 2) * ∂ᵤ G q, E q, F q;
          (1 / 2) * ∂ᵥ G q, F q, G q] -
        Matrix.det !![0, (1 / 2) * ∂ᵥ E q, (1 / 2) * ∂ᵤ G q;
          (1 / 2) * ∂ᵥ E q, E q, F q;
          (1 / 2) * ∂ᵤ G q, F q, G q]) /
      (E q * G q - F q ^ 2) ^ 2 :=
  sorry

/-- **Theorema Egregium** (Pressley, Theorem 10.2.1). Two allowable patches with the same first
fundamental form on `U` have the same Gaussian curvature there. -/
theorem K_eq_of_firstFundamentalMatrix_eq {S S' : Set ℝ³}
    (σ : AllowablePatch S) (σ' : AllowablePatch S') (same_U : σ.U = σ'.U)
    (same_form : ∀ q ∈ σ.U, firstFundamentalMatrix σ.toFun q = firstFundamentalMatrix σ'.toFun q) :
    ∀ q ∈ σ.U, K σ.toFun q = K σ'.toFun q :=
  sorry

/-- **No map of the world is perfect** (Pressley, Proposition 10.2.5). No patch of the sphere has
the first fundamental form of the plane, `E = G = 1` and `F = 0`, because the sphere is curved and
the plane is not. -/
theorem not_flat_spherePatch {r : ℝ} (hr : 0 < r) (σ : AllowablePatch (Metric.sphere (0 : ℝ³) r))
    (hU : σ.U.Nonempty) :
    ¬ ∀ q ∈ σ.U, firstFundamentalMatrix σ.toFun q = 1 :=
  sorry
