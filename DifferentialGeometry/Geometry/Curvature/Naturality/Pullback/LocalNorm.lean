import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalIterCov

noncomputable section

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)

theorem normSq0S_metricRm04At_localPullMetric
    (g : SmoothRiemannianMetric I N) (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f) (x : M) :
    normSq0S (localPullMetric g f hf) x 4 (metricRm04At (localPullMetric g f hf) x) =
      normSq0S g (f x) 4 (metricRm04At g (f x)) := by
  exact Geometry.Tensor.normSq0S_iterCov_localPullMetric g f hf
    (metricRm04 (localPullMetric g f hf)) (metricRm04 g)
    (fun y v => metricRm04StandardAt_localPullMetric g f hf y (v 0) (v 1) (v 2) (v 3)) 0 x

end DifferentialGeometry.Geometry.Curvature
