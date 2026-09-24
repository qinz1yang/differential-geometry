import DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportContinuity
import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime

noncomputable section

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem continuousOn_integral_sq_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {u : ℝ → M → ℝ}
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ)) :
    ContinuousOn
      (fun t => ∫ x, u t x ^ 2 ∂riemannianVolumeMeasure I M (g t)) D.carrier := by
  exact continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    g hg.chartGramMatrix_continuousOn_carrier (fun t x => u t x ^ 2)
    (hu.pow 2) isCompact_univ (fun _ _ _ hx => (hx (mem_univ _)).elim)

theorem continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ)) :
    ContinuousOn
      (fun t => ∫ x, normGradSqFun (g t) (u t) x
        ∂riemannianVolumeMeasure I M (g t)) D.regular := by
  have hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.regular ×ˢ (univ : Set M)) := by
    intro p hp
    exact (hg.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  have hgrad : ContinuousOn
      (fun p : ℝ × M => normGradSqFun (g p.1) (u p.1) p.2)
      (D.regular ×ˢ univ) :=
    (gradSq_joint g D.regular_isOpen
      (chartGramMatrix_joint_contMDiffOn g D.regular hmetric) u hu).continuousOn
  exact continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    g (fun α i j => (hg.chartGramMatrix_continuousOn_carrier α i j).mono
      (prod_mono D.regular_subset Subset.rfl))
    (fun t x => normGradSqFun (g t) (u t) x) hgrad isCompact_univ
    (fun _ _ _ hx => (hx (mem_univ _)).elim)

namespace IsHeatPotOn

theorem continuousOn_integral_sq
    {D : RealTimeInterval} {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u : ℝ → M → ℝ} (hu : IsHeatPotOn D G V u)
    (hG : MetricFamilySmoothOn D G.metric) :
    ContinuousOn
      (fun t => ∫ x, u t x ^ 2 ∂riemannianVolumeMeasure I M (G.metric t))
      D.carrier :=
  continuousOn_integral_sq_of_metricFamilySmoothOn hG hu.jointCont

theorem continuousOn_integral_normGradSqFun
    {D : RealTimeInterval} {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u : ℝ → M → ℝ} (hu : IsHeatPotOn D G V u)
    (hG : MetricFamilySmoothOn D G.metric) :
    ContinuousOn
      (fun t => ∫ x, normGradSqFun (G.metric t) (u t) x
        ∂riemannianVolumeMeasure I M (G.metric t)) D.regular :=
  continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn hG hu.jointSmooth

end IsHeatPotOn

end DifferentialGeometry.Analysis.Parabolic
