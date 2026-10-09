import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopCover

/-!
# Consumers of the sphere loop cover (S-FIXTURE-C2, K2, file 2)

At the circle length `ℓ = 1` the covering `loopCover_FXC2 1` is a surjective covering map, a local
isometry, and the loop distance of two points on one axis `{pole} × [0, 3/10]` is exactly `3/10`
(`loopDist_eq_cyl_of_close_FXC2` with `|0 - 3/10| ≤ 1/2`, then the axis distance of the cylinder).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete

namespace DifferentialGeometry.Geometry.Collapse

/-- The unit-length loop is covered by the cylinder. -/
theorem loopCover_one_covering_FXC2 :
    IsCoveringMap (loopCover_FXC2 1) ∧ Function.Surjective (loopCover_FXC2 1) :=
  loopCover_isCoveringMap_FXC2 1 one_pos

/-- The loop distance of two points of one axis is the axis distance. -/
theorem loopDist_axis_example_FXC2 :
    loopDist_FXC2 1 one_pos (loopCover_FXC2 1 (slimSpherePole, 0))
      (loopCover_FXC2 1 (slimSpherePole, 3 / 10)) = 3 / 10 := by
  have h := loopDist_eq_cyl_of_close_FXC2 1 one_pos (slimSpherePole, 0) (slimSpherePole, 3 / 10)
    (by norm_num [abs_of_neg])
  rw [h, cyl_dist_line_FXC2]
  norm_num [abs_of_neg]

/-- Pythagoras on the cylinder for two axis points of different slices. -/
theorem cyl_sq_dist_example_FXC2 (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    dist ((z, (1 : ℝ)) : sphereCylinder) (slimSpherePole, 0) ^ 2 =
      1 + sphereDist_FXC2 z slimSpherePole ^ 2 := by
  rw [cyl_sq_dist_FXC2]
  norm_num

end DifferentialGeometry.Geometry.Collapse
