import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Metric.ModelChange

namespace DifferentialGeometry.Integral.Measure

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) :
    riemannianVolumeMeasure
        (I := I.transContinuousLinearEquiv e) (M := M) (g.transContinuousLinearEquiv e) =
      riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [SmoothRiemannianMetric.transContinuousLinearEquiv, riemannianVolumeMeasure_pullback_cross]
  exact MeasureTheory.Measure.map_id

end

end DifferentialGeometry.Integral.Measure
