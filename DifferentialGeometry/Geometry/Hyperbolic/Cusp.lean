import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Hyperbolic.CuspCurvatureFields

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature GC.Endpoint
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Hyperbolic

abbrev CuspHalfSpace := Torus × EuclideanHalfSpace 1

def cuspDepth : ℝ := 100

def cuspDomain : Set CuspHalfSpace := {p | p.2.val 0 < cuspDepth}

structure HyperbolicCusp where
  torusMetric : SmoothRiemannianMetric torusModel Torus
  torus_flat : ∀ (p : Torus) (v w : TangentSpace torusModel p),
    metricRm04StandardAt torusMetric p v w w v = 0
  metric : SmoothRiemannianMetric halfCollarModel CuspHalfSpace
  metric_formula : ∀ (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p),
    metric.inner p v w = v.2 0 * w.2 0 +
      Real.exp (-p.2.val 0) * torusMetric.inner p.1 v.1 w.1

theorem cusp_constant_sectional_curvature (H : HyperbolicCusp)
    (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p) :
    metricRm04StandardAt H.metric p v w w v =
      -(1 / 4 : ℝ) * (H.metric.inner p v v * H.metric.inner p w w -
        H.metric.inner p v w ^ 2) := by
  exact cusp_constant_sectional_curvature_of_fields H.torusMetric H.torus_flat H.metric
    H.metric_formula p v w

end DifferentialGeometry.Geometry.Hyperbolic
