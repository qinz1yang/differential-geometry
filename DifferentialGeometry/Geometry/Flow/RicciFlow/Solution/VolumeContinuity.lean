import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ChartGramContinuity
import DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

noncomputable section

open Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

namespace SolutionOn

theorem continuousOn_volume (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    ContinuousOn (fun t => (riemannianVolumeMeasure I M (S.family.metric t) univ).toReal)
      D.carrier := by
  have hi := continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    S.family.metric
    hS.smoothMetric.metricTensor_cont.continuousOn_chartGram
    (fun _ _ => (1 : ℝ)) continuousOn_const isCompact_univ
    (fun _ _ _ hx => (hx (mem_univ _)).elim)
  simpa only [integral_const, smul_eq_mul, mul_one, Measure.real_def] using hi

end SolutionOn

end DifferentialGeometry.PDE.RicciFlow
