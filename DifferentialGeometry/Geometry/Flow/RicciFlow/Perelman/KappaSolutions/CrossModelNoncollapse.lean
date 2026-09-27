import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelBallTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelCurvatureTransport

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal

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

private local instance crossModelNoncollapseMeasurableM : MeasurableSpace M := borel M
private local instance crossModelNoncollapseBorelM : BorelSpace M := ⟨rfl⟩
private local instance crossModelNoncollapseMeasurableN : MeasurableSpace N := borel N
private local instance crossModelNoncollapseBorelN : BorelSpace N := ⟨rfl⟩
private local instance crossModelNoncollapseC1M : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance crossModelNoncollapseC1N : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem tensor_noncollapsed_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (kappa : ℝ) (n : ℕ)
    (hnoncollapse : ∀ (p : N) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := J) g p r,
        r ^ 4 * normSq0S (I := J) g y 4 (metricRm04At (I := J) g y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ n ≤
        riemannianVolumeMeasure (I := J) (M := N) g
          (riemannianBallOf (I := J) g p r))
    (x : M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ y ∈
      riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r,
      r ^ 4 * normSq0S (I := I) (Diffeomorph.pullbackMetricCross g Phi) y 4
        (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) y) ≤ 1) :
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ n ≤
      riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross g Phi)
        (riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r) := by
  rw [riemannianBallOf_volume_pullbackMetricCross]
  apply hnoncollapse (Phi x) r hr
  intro y hy
  rw [← image_riemannianBallOf_pullbackMetricCross g Phi x r] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simpa only [metricRmNormSq_pullbackCross] using hcurvature z hz

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
