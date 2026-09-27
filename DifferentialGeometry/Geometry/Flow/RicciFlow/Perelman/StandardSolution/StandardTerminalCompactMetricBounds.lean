import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalCompactFlows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MixedMetricBounds
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem standard_uniform_terminal_compact_metric_bounds :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L D A : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧ (∀ N, 0 ≤ D N) ∧ (∀ N, 0 < A N) ∧
      ∃ ell : ℝ, 0 < ell ∧ ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ B : ℕ → ℝ,
      (∀ N, 0 ≤ B N) ∧ ∃ ΛZ : ℝ, 1 ≤ ΛZ ∧ ∃ CZ LZ : ℕ → ℝ,
      (∀ N, 0 ≤ CZ N) ∧ (∀ N, 0 ≤ LZ N) ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
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
          (∀ t ∈ Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Icc 0 T) t) ∧
          (∀ (R : ℝ) (hR : 2 < R),
            RiemannianMetricComplete (metricTruncation (G T) R hR) ∧
            (∀ (x : E3) (v : TangentSpace (𝓡 3) x),
              ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
                (metricTruncation (G T) R hR).inner x v v) ∧
            (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ (v w : TangentSpace (𝓡 3) x),
              (metricTruncation (G T) R hR).inner x v w = (G T).inner x v w) ∧
            (∀ (x : E3), R - 1 ≤ ‖x‖ → ∀ (v w : TangentSpace (𝓡 3) x),
              (metricTruncation (G T) R hR).inner x v w =
                DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v w)) ∧
          (∀ (R : ℝ) (hR : 2 < R), transitionEnd + 4 ≤ R →
            (∀ N j : ℕ, j ≤ N → ∀ x : E3,
              metricDerivNorm j (metricTruncation (G T) R hR)
                DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D N) ∧
            (∀ k : ℕ, ∀ x : E3,
              Real.sqrt (normSq0S (metricTruncation (G T) R hR) x (4 + k)
                (iterCov (metricTruncation (G T) R hR) 4
                  (metricRm04 (metricTruncation (G T) R hR)) k x)) ≤ A k)) ∧
          ∀ (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R),
            transitionEnd + 4 ≤ R →
            ∃ Z : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
              IsSolutionOn Z ∧ Z.base.metric 0 = compactDoubleTruncationMetric north R hR (G T) ∧
              (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (Z.base.metric t)) ∧
              (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
                ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                  (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (Z.base.metric p.1) x₀ p.2 i j)
                  (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
              (∀ t ∈ Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
                HasDerivWithinAt (fun r => (Z.base.metric r).inner x v w)
                  (-2 * ricciTensor (Z.base.metric t) x v w) (Ici 0) t) ∧
              (∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 τ, ∀ x : S3,
                Real.sqrt (normSq0S (Z.base.metric t) x (4 + a)
                  (iteratedCovariantTimeDerivWithin Z.base.metric
                    (fun r => nablaKRm04Field Z r a x) (Icc 0 τ) b t)) ≤ B N) ∧
              (∀ x ∈ Metric.ball (0 : E3) (R + 1), ∀ v w : E3,
                (Z.base.metric 0).inner (compactDoubleCapMap north R x)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                    (metricTruncation (G T) R (by linarith [le_max_right transitionEnd 2])).inner x v w) ∧
              (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ v w : E3,
                (Z.base.metric 0).inner (compactDoubleCapMap north R x)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                    (G T).inner x v w) ∧
              (∀ t ∈ Icc 0 τ, MetricUniformEquivalentOn univ
                (Z.base.metric 0) (Z.base.metric t) ΛZ) ∧
              (∀ N : ℕ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
                metricCovDerivNorm N (Z.base.metric t) (Z.base.metric 0) x ≤ CZ N) ∧
              ∀ N : ℕ, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
                metricDerivNorm N (Z.base.metric s) (Z.base.metric t)
                  (Z.base.metric 0) x ≤ LZ N * |s - t| := by
  obtain ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, hfamily⟩ := standard_uniform_terminal_compact_flows
  obtain ⟨ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, henrich⟩ :=
    exists_uniform_metric_time_bounds_of_spatial_curvature_bounds
      (I := 𝓡 3) (M := S3) (by simp) τ hτ B hB
  refine ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, ?_⟩
  intro S T hT hTα hTS
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, hflows⟩ := hfamily S T hT hTα hTS
  refine ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, ?_⟩
  intro north R hR hlarge
  obtain ⟨Z, hZ, hz, hcomp, hg, hp, hm, hfull, hcore⟩ := hflows north R hR hlarge
  have hspatial (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (x : S3) :
      Real.sqrt (normSq0S (Z.base.metric t) x (4 + k)
        (nablaKRm04Field Z t k x)) ≤ B k := by
    exact hm k k 0 (by omega) t ht x
  obtain ⟨heZ, hcZ, hlZ⟩ := henrich Z hZ hg hp hspatial
  exact ⟨Z, hZ, hz, hcomp, hg, hp, hm, hfull, hcore, heZ, hcZ, hlZ⟩
end DifferentialGeometry.PDE.RicciFlow
