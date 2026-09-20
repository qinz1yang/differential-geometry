import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Analysis.Integration.Measure.ModelChange

open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem normalizedShrinkerMass_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (f : M → ℝ) :
    normalizedShrinkerMass (g.transContinuousLinearEquiv e) f = normalizedShrinkerMass g f := by
  unfold normalizedShrinkerMass
  rw [← e.toLinearEquiv.finrank_eq,
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_transContinuousLinearEquiv]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
