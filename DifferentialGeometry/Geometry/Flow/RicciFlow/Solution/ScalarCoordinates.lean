import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]

theorem SolutionOn.scalar_chartTrace_eq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    S.scalar t ((extChartAt I p).symm y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (S.base.metric t) p i j y *
          chartRicciTensor (I := I) (S.base.metric t) p i j y := by
  have hx : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact (extChartAt I p).map_target hy
  change metricScalarAt (I := I) (S.base.metric t) ((extChartAt I p).symm y) = _
  rw [metricScalar_chartTrace_eq (S.base.metric t) p hx]
  simp only [(extChartAt I p).right_inv hy]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa only [(extChartAt I p).right_inv hy] using
    ricciTensor_chartBasisVec_alpha_eq (S.base.metric t) p i j hx

end DifferentialGeometry.PDE.RicciFlow
