import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCenterSplittingExclusion
import DifferentialGeometry.Geometry.Metric.Approximation.RealSplitting

/-!
# Consumer of EGP01: the Euclidean plane has no strong edge point at its origin

The identity of the plane is an actual `(2, β)`-splitting; EGP01 then rules out every strong edge
predicate there (qualities `b, s < 10⁻⁶`, any `Δ`). The half-plane chart is not assumed.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe v

theorem plane_origin_not_isEdgePoint {Δ b s : ℝ} (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) :
    ¬ isEdgePoint.{0, v} (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) Δ b s := fun h =>
  not_hasEuclideanSplitting_two_of_isEdgePoint.{0, v, 0} h hb hs
    (by norm_num : (1 / 2000000 : ℝ) < 1 / 1000000)
    (hasEuclideanSplitting_two_of_plane_approximation
      ((IsometryEquiv.refl (WithLp 2 (ℝ × ℝ))).toKleinerLottApprox rfl
        (by norm_num : (0 : ℝ) < 1 / 2000000) (by norm_num)))

end GC.MetricGeometry
