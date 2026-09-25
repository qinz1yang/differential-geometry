import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter

noncomputable section

open Set Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hG : chartGramFamilySmoothWithinOn (I := I) g p J) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (metricScalarAt (g z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (g z.1) p i j z.2 * chartRicciTensor (g z.1) p i j z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
    intro z hz
    exact ContDiffWithinAt.sum fun i _ => ContDiffWithinAt.sum fun j _ =>
      (chartInvGramOnE_contDiffWithinAt g p hG i j hz.1 hz.2).mul
        (chartRicciTensor_contDiffWithinAt g p hG i j hz.1 hz.2)
  apply hs.congr
  intro z hz
  have hy := interior_subset hz.2
  have hx : (extChartAt I p).symm z.2 ∈ chartLeviCivitaGoodSet (I := I) p := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact (extChartAt I p).map_target hy
  change metricScalarAt (g z.1) ((extChartAt I p).symm z.2) = _
  rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq (g z.1) p hx]
  simp only [(extChartAt I p).right_inv hy]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa only [(extChartAt I p).right_inv hy] using
    ricciTensor_chartBasisVec_alpha_eq (g z.1) p i j hx

end DifferentialGeometry.Geometry.Curvature

end
