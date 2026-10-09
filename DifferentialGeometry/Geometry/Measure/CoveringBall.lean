import DifferentialGeometry.Geometry.Measure.LocalIsometryOn
import DifferentialGeometry.Geometry.Metric.Covering.BallImage

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Measure

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_eq_of_injOn_coveringMap
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {p : M → N} (hp : IsLocalDiffeomorph I J ∞ p) (hcover : IsCoveringMap p)
    (hpull : localPullMetric h p hp = g) (x : M) (r : ℝ)
    (hinj : Set.InjOn p (riemannianBallOf g x r)) :
    riemannianVolumeMeasure I M g (riemannianBallOf g x r) =
      riemannianVolumeMeasure J N h (riemannianBallOf h (p x) r) := by
  have hopen : IsOpen (riemannianBallOf g x r) :=
    isOpen_lt (Riemannian.continuous_riemannianEDist g x) continuous_const
  let U : TopologicalSpace.Opens M := ⟨riemannianBallOf g x r, hopen⟩
  have hmetric (z : M) (_ : z ∈ U) (v w : TangentSpace I z) :
      g.inner z v w = h.inner (p z) (mfderiv I J p z v) (mfderiv I J p z w) := by
    rw [← hpull, localPullMetric_inner]
  have hvol := riemannianVolumeMeasure_image_eq_of_injOn_local_isometry g h p U
    (hp.isLocalDiffeomorphOn U) hinj hmetric hopen.measurableSet Set.Subset.rfl
  rwa [Metric.image_riemannianBallOf_of_coveringMap_localPullMetric g h hp hcover hpull x r] at hvol

end DifferentialGeometry.Geometry.Measure
