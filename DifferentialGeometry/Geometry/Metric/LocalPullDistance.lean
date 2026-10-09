import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

noncomputable section

open Set Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem riemannianEDistOf_localPullMetric_eq_of_ball_subset
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (p : M) {R : ℝ≥0} (hR : 0 < R)
    (hball : {x : N | riemannianEDistOf g (f p) x < R} ⊆ range f)
    (x : M) (hx : riemannianEDistOf g (f p) (f x) < (R / 3 : ℝ≥0)) :
    riemannianEDistOf (localPullMetric g f hf) p x =
      riemannianEDistOf g (f p) (f x) := by
  let Φ := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage f hf hinj
  have hmetric : localPullMetric g f hf =
      pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, pullbackMetricOfInjectiveLocalDiffeomorph_inner]
  rw [hmetric, pullbackMetricOfInjectiveLocalDiffeomorph,
    edistOf_pullbackMetricCross]
  have hp : riemannianEDistOf g (f p) (f p) < (R / 3 : ℝ≥0) := by
    rw [riemannianEDistOf_self]
    exact_mod_cast (div_pos hR (by norm_num : (0 : ℝ≥0) < 3))
  exact riemannianEDistOf_restrictOpen_eq_of_ball_subset
    g hf.image (f p) R hball (Φ p) (Φ x) hp hx

end DifferentialGeometry.Geometry.Metric
