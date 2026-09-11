import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLeviCivitaLimit
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Endomorphism


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.TensorLieDeriv
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ancientCovariantC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance ancientCovariantC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem solution_connectionEndomorphism_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (p : M) (y : E) :
    ContinuousWithinAt
      (fun s => connectionEndomorphismInChartL (S.family.connection s) p y) (Iic b) t := by
  classical
  apply continuousWithinAt_clm_apply.mpr
  intro X
  apply continuousWithinAt_clm_apply.mpr
  intro v
  by_cases hy : y ∈ (extChartAt I p).target
  · simp only [connectionEndomorphismInChartL_apply_of_mem _ p hy]
    have hbase : (extChartAt I p).symm y ∈
        (trivializationAt E (TangentSpace I) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt I p).map_target hy
    exact ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ
      ((extChartAt I p).symm y)).continuous.continuousAt.comp_continuousWithinAt
        (solution_leviCivita_continuousWithinAt S hS hcarrier hregular ht
          (tangentConstInChart p v) ((extChartAt I p).symm y)
          (mdifferentiableAt_tangentConstInChart_of_mem v hbase) _)
  · simp only [connectionEndomorphismInChartL_apply_of_notMem _ p hy]
    exact continuousWithinAt_const

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
