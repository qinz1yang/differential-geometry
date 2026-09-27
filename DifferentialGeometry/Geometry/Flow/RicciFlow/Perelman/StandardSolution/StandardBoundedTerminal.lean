import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Metric.TerminalFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem standard_smooth_terminal_families_of_curvature_bound
    (T K : ℝ) (hT : 0 < T) (hK : 0 ≤ K) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ENNReal.ofReal T ≤ S.lifetime →
        (∀ t ∈ Ico 0 T, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ Icc 0 T, MetricUniformEquivalentOn univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          (∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Ici 0) t) ∧
          (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (G p.1) x₀ p.2 i j)
              (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          ∀ t ∈ Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Icc 0 T) t := by
  obtain ⟨Λ, hΛ, C, L, hC, hL, hb⟩ :=
    standard_metric_bounds_before_endpoint T K hT.le hK
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S hTS hRm
  obtain ⟨he, hc, hl⟩ := hb S hTS hRm
  obtain ⟨G, hEq, hComp, hEquiv, hCov, hLip, hJets⟩ :=
    exists_closed_terminal_family_of_reference_bounds (I := 𝓡 3) (M := E3)
      inferInstance DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete
      S.metric T Λ hT hΛ C L hL he hc hl
  have hpde : ∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (G s).inner x v w)
        (-2 * ricciTensor (G t) x v w) (Ici 0) t := by
    intro t ht x v w
    have hdom : t ∈ S.domain := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).mpr ht.2 |>.trans_le hTS⟩
    have hgerm : (fun s => (G s).inner x v w) =ᶠ[𝓝[Ici 0] t]
        (fun s => (S.metric s).inner x v w) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsT
      rw [hEq s ⟨hs, hsT⟩]
    rw [hEq t ht]
    exact (S.equation t hdom x v w).congr_of_eventuallyEq hgerm (by rw [hEq t ht])
  obtain ⟨hgram, hclosed⟩ := contMDiffOn_and_equation_Icc_of_spatial_jets G 0 T hT hJets
    (fun t ht x v w => (hpde t ⟨ht.1.le, ht.2⟩ x v w).hasDerivAt (Ici_mem_nhds ht.1))
  exact ⟨G, hEq, (hEq 0 ⟨le_rfl, hT⟩).trans S.initial, hComp, hEquiv,
    hCov, hLip, hJets, hpde, hgram, hclosed⟩
end DifferentialGeometry.PDE.RicciFlow
