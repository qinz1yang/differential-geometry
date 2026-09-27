import DifferentialGeometry.Geometry.Metric.Family.Cartesian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMaximalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_standard_solution_extending_bounded_flow
    {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := E3) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioo 0 T ⊆ D.regular)
    (hinitial : S.base.metric 0 = StandardCap.metric)
    (hgram : ∀ (x : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x).baseSet))
    {C : ℝ} (hcurv : ∀ t ∈ Icc 0 T, ∀ x : E3,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C) :
    ∃ Q : StandardSolution, ENNReal.ofReal T ≤ Q.val.lifetime ∧
      ∀ t ∈ Ico 0 T, Q.val.metric t = S.base.metric t := by
  have hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (S.base.metric t) := by
    intro t ht
    apply complete_of_curvature_bound S hS hslab hreg hcurv ht ⟨le_rfl, hT.le⟩
    rw [hinitial]
    exact StandardCap.metric_complete
  have hdomain : (lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)).carrier =
      Ico 0 T := by rw [lifetimeInterval_ofReal T hT]; rfl
  let P : PartialStandardSolution := {
    lifetime := ENNReal.ofReal T
    lifetime_pos := ENNReal.ofReal_pos.mpr hT
    metric := S.base.metric
    smooth := by
      rw [hdomain]
      exact (cartesian_contDiffOn_of_chartGram S.base.metric (Icc 0 T) hgram).mono
        (prod_mono Ico_subset_Icc_self Subset.rfl)
    equation := by
      rw [hdomain]
      intro t ht x v w
      apply (metricPDE_Icc S hS hslab hreg t (Ico_subset_Icc_self ht) x v w).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)]
        with r hr hrT
      exact ⟨hr,hrT.le⟩
    initial := hinitial
    complete := fun t ht => hcomplete t (Ico_subset_Icc_self (hdomain ▸ ht))
    curvature_bound := by
      intro a _ ha
      have haT : a < T := (ENNReal.ofReal_lt_ofReal_iff hT).mp ha
      exact ⟨Real.sqrt C, Real.sqrt_nonneg _, fun t ht x =>
        Real.sqrt_le_sqrt (hcurv t ⟨ht.1, ht.2.trans haT.le⟩ x)⟩ }
  obtain ⟨Q, hQ⟩ := P.exists_maximal_extension
  refine ⟨Q, hQ.1, fun t ht => hQ.2 t ?_⟩
  change t ∈ (lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)).carrier
  rwa [hdomain]

end DifferentialGeometry.PDE.RicciFlow
