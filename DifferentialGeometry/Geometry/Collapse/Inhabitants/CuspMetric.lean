import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Metric.WarpedProduct.Exponential
import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
An actual flat torus metric and its exponential half-cusp provide the metric data for
truncated cusp inhabitants without a flatness or metric-formula premise.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

def standardCuspCircleMetric : SmoothRiemannianMetric (𝓡 1) Circle :=
  Diffeomorph.pullbackMetricCross AddCircle.flatMetric AddCircle.diffeomorphCircle.symm

def standardCuspTorusMetric : SmoothRiemannianMetric torusModel Torus :=
  standardCuspCircleMetric.prod standardCuspCircleMetric

theorem standardCuspTorusMetric_flat (p : Torus) (v w : TangentSpace torusModel p) :
    metricRm04StandardAt standardCuspTorusMetric p v w w v = 0 := by
  change metricRm04At (standardCuspCircleMetric.prod standardCuspCircleMetric) p
    (vec4 v w w v) = 0
  rw [metricRm04At_productMetric_apply,
    metricRm04At_eq_zero_of_finrank_le_one standardCuspCircleMetric (by simp) p.1,
    metricRm04At_eq_zero_of_finrank_le_one standardCuspCircleMetric (by simp) p.2]
  erw [DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.zero_apply]
  exact zero_add 0

def standardHyperbolicCusp : HyperbolicCusp where
  torusMetric := standardCuspTorusMetric
  torus_flat := standardCuspTorusMetric_flat
  metric := standardCuspTorusMetric.exponentialWarpedEnd (1 / 2)
  metric_formula := by
    intro p v w
    rw [SmoothRiemannianMetric.exponentialWarpedEnd_inner]
    rw [show -2 * (1 / 2 : ℝ) * p.2.val 0 = -p.2.val 0 by ring]

theorem standardHyperbolicCusp_inner (p : CuspHalfSpace)
    (v w : TangentSpace halfCollarModel p) :
    standardHyperbolicCusp.metric.inner p v w = v.2 0 * w.2 0 +
      Real.exp (-p.2.val 0) * standardCuspTorusMetric.inner p.1 v.1 w.1 :=
  standardHyperbolicCusp.metric_formula p v w

end DifferentialGeometry.Geometry.Collapse
