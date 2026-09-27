import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance upstreamCrossVolumeMeasurableM : MeasurableSpace M := borel M
private local instance upstreamCrossVolumeBorelM : BorelSpace M := ⟨rfl⟩
private local instance upstreamCrossVolumeMeasurableN : MeasurableSpace N := borel N
private local instance upstreamCrossVolumeBorelN : BorelSpace N := ⟨rfl⟩
private local instance upstreamCrossVolumeC1M : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance upstreamCrossVolumeC1N : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] [CompleteSpace F] in
theorem volumeMeasurePreserving_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) :
    MeasurePreserving (Phi : M → N)
      (riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross g Phi))
      (riemannianVolumeMeasure (I := J) (M := N) g) := by
  have h := riemannianVolumeMeasure_pullback_cross (I := I) (J := J) g Phi
  refine ⟨Phi.continuous.measurable, ?_⟩
  rw [h, Measure.map_map Phi.continuous.measurable Phi.symm.continuous.measurable]
  simp only [Function.comp_def, Phi.apply_symm_apply, Measure.map_id']

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
