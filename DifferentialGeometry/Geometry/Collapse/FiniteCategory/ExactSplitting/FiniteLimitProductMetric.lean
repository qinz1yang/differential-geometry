import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.FiniteLimitSplitting
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductDistanceApplications

/-!
# R2 on a finite Cheeger–Gromov limit: the finite-order product metric

The missing input (R2) of LFR18/LFR20 (build-logs/worker-F7-DOWN.md, "Recorded obstructions"):
the finite limit `N` of LFR14–LFR15 (metric `G` of natural order `K - 1`, `K ≥ 4`, as its
Riemannian structure) with an exact splitting `e : N ≃ᵢ ℓ²(F × W)` carries the `C^{K-1}`
product metric `κ = du² + h` on `F × Z` (`Z = t⁻¹(0)` with its `C^K` atlas and induced metric `h`):
* `κ` is the pullback of `G` by the actual `C^K` product map `Ψ`;
* the Riemannian distance of `κ` is the `ℓ²` product distance, and `Ψ` is a distance isometry
  `ℓ²(F × Z) → N` (so `e` is the distance isometry of the product structure).
`finiteLimit_productMetric` (any model space, any rank of `F`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {N W : Type*} [MetricSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [CompleteSpace N]
  [MetricSpace W]

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

/-- **R2 on a finite limit.** The `C^{K-1}` product metric `κ = du² + h` on `F × Z`
(`splittingProductMetric` at the re-indexed order) is `Ψ^* G`, its Riemannian distance is the `ℓ²`
distance, and `Ψ : ℓ²(F × Z) → N` is a distance isometry. -/
theorem finiteLimit_productMetric (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E) N)
    (e : N ≃ᵢ WithLp 2 (F × W)) :
    letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
    letI := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
      (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
    letI := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
      (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
    letI : RiemannianBundle (TangentSpace IP : F × {x : N // (e x).fst = 0} → Type _) :=
      ⟨(splittingProductMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
        (finiteOrderMetricReindex_enorm K hK G) e).toRiemannianMetric⟩
    (∀ (p : F × {x : N // (e x).fst = 0}) (v w : TangentSpace IP p),
      (splittingProductMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
        (finiteOrderMetricReindex_enorm K hK G) e).inner p v w =
        inner ℝ v.1 w.1 + (inducedMetric (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).inner
            p.2 v.2 w.2) ∧
    (∀ (p : F × {x : N // (e x).fst = 0}) (v w : TangentSpace IP p),
      G.inner (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
        (mfderiv IP 𝓘(ℝ, E) (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) p v)
        (mfderiv IP 𝓘(ℝ, E) (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) p w) =
      (splittingProductMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
        (finiteOrderMetricReindex_enorm K hK G) e).inner p v w) ∧
    (∀ p q : F × {x : N // (e x).fst = 0},
      riemannianEDist IP p q = edist (toLp 2 p) (toLp 2 q)) ∧
    (∀ p q : F × {x : N // (e x).fst = 0},
      dist (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
        (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e q) =
        dist (toLp 2 p) (toLp 2 q)) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E) N := hRiem
  let _ := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  let _ := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  have hinner := splittingProductMetric_inner (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  have hmetric := splittingProductDiffeomorph_metric (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  have hdist := splittingProductMetric_riemannianEDist (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  have happly := splittingProductDiffeomorph_apply (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  refine ⟨hinner, fun p v w => (hmetric p v w).trans (hinner p v w).symm, hdist,
    fun p q => ?_⟩
  rw [happly p, happly q]
  exact (splittingFactorProductEquiv e).dist_eq _ _

end DifferentialGeometry.Geometry.ExactSplitting
