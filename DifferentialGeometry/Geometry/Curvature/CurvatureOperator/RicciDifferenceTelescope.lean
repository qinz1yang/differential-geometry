import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature

/-!
# The telescoped Ricci-difference identity of two Riemannian metrics over a common background

Given three smooth Riemannian metrics `g₀, g₁, g₂` on a closed manifold `M`, the difference of
the two Ricci tensors `Ric^{g₁} - Ric^{g₂}` is telescoped against the common background `g₀`:
$$
  \mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₂}(v, w)
    = \bigl[\mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₀}(v, w)\bigr]
      - \bigl[\mathrm{Ric}^{g₂}(v, w) - \mathrm{Ric}^{g₀}(v, w)\bigr],
$$
and each bracket is expanded into the difference-tensor terms via the basis-summed Ricci-difference
corollary `ricciTensor_sub_eq_basisSum_difference` of
`ConnectionDifferenceCurvature.lean`.  Merging the two basis sums collects the expansion into a
single model-basis trace of **per-term differences**:
$$
  \mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₂}(v, w)
    = \sum_i \bigl[\,b\bigr]_i\Bigl(\mathrm{summand}^{g₀,g₁}_i - \mathrm{summand}^{g₀,g₂}_i\Bigr),
$$
where each `summand^{g₀,gₖ}_i` is the grouped per-slot difference-tensor expression
`(∇₀_{B_i} Dₖ)(V, W) - (∇₀_V Dₖ)(B_i, W) + Dₖ(B_i, Dₖ(V, W)) - Dₖ(V, Dₖ(B_i, W))` of the
connection difference `Dₖ = CovariantDerivative.difference (LeviCivita gₖ) (LeviCivita g₀)`.

This is the **identity layer** of the metric-difference (DeTurck) Faà-di-Bruno telescoping of the
sealed Ricci nonlinearity: it exhibits the Ricci difference at a point as a basis trace whose every
summand is a *difference of two difference-tensor expansions*, the entry point at which the
connection-difference cocycle `D₁ - D₂ = connDiff g₁ g₂` makes each summand carry a single
metric-difference factor.  The summand is the genuine per-term expansion of
`ConnectionDifferenceCurvature.lean`; this file supplies only the two-metric telescope and the
basis-sum merge, both pure additive algebra over that expansion.

## Main definitions

* `ricciDiffBasisSummand g₀ gₖ x v w i` — the per-slot grouped difference-tensor summand of the
  single-metric Ricci difference `Ric^{gₖ} - Ric^{g₀}` at the model-basis index `i`, i.e. the
  `i`-th summand vector of `ricciTensor_sub_eq_basisSum_difference`.

## Main theorems

* `ricciTensor_sub_eq_basisSum_summand` — the single-metric Ricci difference as the model-basis
  trace of `ricciDiffBasisSummand` (the named-summand restatement of
  `ricciTensor_sub_eq_basisSum_difference`).
* `ricciTensor_sub_telescope` — **the telescoped two-metric identity**: `Ric^{g₁} - Ric^{g₂}` at a
  point is the model-basis trace of the per-term summand differences
  `ricciDiffBasisSummand g₀ g₁ ⋯ i - ricciDiffBasisSummand g₀ g₂ ⋯ i`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open VectorField
open DifferentialGeometry.Integral.Measure

section Ricci

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The per-slot grouped difference-tensor summand of the single-metric Ricci difference.**

For two smooth Riemannian metrics `g₀, gₖ`, fibre vectors `v, w ∈ T_x M`, and a model-basis index
`i`, this is the `i`-th summand vector of `ricciTensor_sub_eq_basisSum_difference`: the grouped
covariant-derivative-of-difference plus quadratic difference-tensor expression
$$
  (∇₀_{B_i} D_k)(V, W) - (∇₀_V D_k)(B_i, W) + D_k(B_i, D_k(V, W)) - D_k(V, D_k(B_i, W)),
$$
where `D_k = CovariantDerivative.difference (LeviCivita gₖ) (LeviCivita g₀)`,
`B_i = smoothExtensionTangent x (chartModelBasis E i)`, `V = smoothExtensionTangent x v`,
`W = smoothExtensionTangent x w`.  The Ricci difference at `x` is the model-basis trace
`∑ i, (chartModelBasis E).repr (ricciDiffBasisSummand g₀ gₖ x v w i) i`
(`ricciTensor_sub_eq_basisSum_summand`). -/
def ricciDiffBasisSummand (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x
      - covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x)
    + (CovariantDerivative.difference (LeviCivita (I := I) gₖ) (LeviCivita (I := I) g₀) x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w) x)
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
        - CovariantDerivative.difference (LeviCivita (I := I) gₖ)
            (LeviCivita (I := I) g₀) x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w) x)
          (smoothExtensionTangent (I := I) x v x))

/-- **The single-metric Ricci difference as the model-basis trace of `ricciDiffBasisSummand`.**
This is the named-summand restatement of `ricciTensor_sub_eq_basisSum_difference`: the difference of
the two Ricci tensors at `x` is the model-basis trace of the per-slot grouped difference-tensor
summand. -/
theorem ricciTensor_sub_eq_basisSum_summand (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) gₖ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (ricciDiffBasisSummand (I := I) g₀ gₖ x v w i) i := by
  rw [ricciTensor_sub_eq_basisSum_difference (I := I) g₀ gₖ x v w]
  rfl

/-- **The telescoped two-metric Ricci-difference identity.**

For three smooth Riemannian metrics `g₀, g₁, g₂`, the difference of the two Ricci tensors at `x` is
the model-basis trace of the **per-term differences** of the grouped difference-tensor summands of
`Ric^{g₁} - Ric^{g₀}` and `Ric^{g₂} - Ric^{g₀}`:
$$
  \mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₂}(v, w)
    = \sum_i \bigl[\,b\bigr]_i\Bigl(\mathrm{summand}^{g₀,g₁}_i - \mathrm{summand}^{g₀,g₂}_i\Bigr).
$$

The proof telescopes the two-metric difference against the common background `g₀`
(`Ric^{g₁} - Ric^{g₂} = (Ric^{g₁} - Ric^{g₀}) - (Ric^{g₂} - Ric^{g₀})`), expands each bracket by
`ricciTensor_sub_eq_basisSum_summand`, and merges the two basis sums by linearity of the coordinate
functional `(chartModelBasis E).repr` (`map_sub`, `Finsupp.sub_apply`).  This is the identity layer
the metric-difference Faà-di-Bruno telescoping of the sealed Ricci nonlinearity consumes: each
summand difference `summand^{g₀,g₁}_i - summand^{g₀,g₂}_i` is the point at which the
connection-difference cocycle `D₁ - D₂ = connDiff g₁ g₂` isolates a single metric-difference
factor. -/
theorem ricciTensor_sub_telescope (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₂ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
            - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i) i := by
  have h1 := ricciTensor_sub_eq_basisSum_summand (I := I) g₀ g₁ x v w
  have h2 := ricciTensor_sub_eq_basisSum_summand (I := I) g₀ g₂ x v w
  have key : ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₂ x v w =
      (ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w)
        - (ricciTensor (I := I) g₂ x v w - ricciTensor (I := I) g₀ x v w) := by ring
  rw [key, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (chartModelBasis E).repr
        (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
          - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i)
        = (chartModelBasis E).repr (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i)
          - (chartModelBasis E).repr (ricciDiffBasisSummand (I := I) g₀ g₂ x v w i)
      from map_sub _ _ _, Finsupp.sub_apply]

end Ricci

end Connection
end Integral
end DifferentialGeometry
