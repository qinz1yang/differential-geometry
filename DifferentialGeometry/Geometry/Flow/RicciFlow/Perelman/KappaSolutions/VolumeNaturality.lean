import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Comparison.Volume.DiffeomorphVolume

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] in
theorem volumeMeasurePreserving_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    MeasurePreserving (Phi : M → N)
      (riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetric g Phi))
      (riemannianVolumeMeasure (I := I) (M := N) g) := by
  exact Geometry.Riemannian.VolumeComparison.measurePreserving_riemannianVolume_pullback g Phi

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
