import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.VolumeNaturality
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [CompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] in
theorem integral_pullbackMetric_comp
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) (f : N → ℝ) :
    (∫ x, f (Phi x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetric g Phi))) =
      ∫ y, f y ∂(riemannianVolumeMeasure (I := I) (M := N) g) :=
  (volumeMeasurePreserving_pullbackMetric g Phi).integral_comp
    Phi.toHomeomorph.measurableEmbedding f


omit [CompleteSpace E] in
theorem surfaceArea_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    surfaceArea (Diffeomorph.pullbackMetric g Phi) = surfaceArea g := by
  have h := integral_pullbackMetric_comp g Phi (fun _ => (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, surfaceArea] using h

variable [BoundarylessManifold I M] [BoundarylessManifold I N]


theorem totalScalarCurvature_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    totalScalarCurvature (Diffeomorph.pullbackMetric g Phi) = totalScalarCurvature g := by
  unfold totalScalarCurvature
  simp_rw [metricScalarAt_pullback]
  exact integral_pullbackMetric_comp g Phi (fun y => metricScalarAt (I := I) g y)

theorem surfaceEntropy_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    surfaceEntropy (Diffeomorph.pullbackMetric g Phi) = surfaceEntropy g := by
  unfold surfaceEntropy
  simp_rw [metricScalarAt_pullback, surfaceArea_pullbackMetric]
  exact integral_pullbackMetric_comp g Phi
    (fun y => metricScalarAt (I := I) g y *
      Real.log (metricScalarAt (I := I) g y * surfaceArea g))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
