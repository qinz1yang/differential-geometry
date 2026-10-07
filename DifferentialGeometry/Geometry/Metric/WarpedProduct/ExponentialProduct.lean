import DifferentialGeometry.Geometry.Metric.WarpedProduct.Exponential
import DifferentialGeometry.Geometry.Metric.EuclideanHalfSpace

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exponentialWarpedEnd_zero_eq_prod (g : SmoothRiemannianMetric I M) :
    g.exponentialWarpedEnd 0 =
      g.prod (euclideanHalfSpaceMetric 1) := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  erw [SmoothRiemannianMetric.exponentialWarpedEnd_inner,
    SmoothRiemannianMetric.prod_inner,
    euclideanHalfSpaceMetric_inner]
  simp [PiLp.inner_apply, add_comm, mul_comm]

end DifferentialGeometry.SmoothRiemannianMetric
