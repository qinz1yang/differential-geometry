import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Geometry.Curvature.WarpedProduct.Exponential

/-!
# The reference cusp has constant sectional curvature `-1/4`

The metric `dz² + e^{-z} g_T` on `T² × [0, ∞)` with a flat torus metric `g_T` is the exponential
warped end of `g_T` with rate `1/2`; the warped-product curvature formula gives sectional curvature
`-1/4`. The statement is unbundled over the four fields of `HyperbolicCusp`
(`Geometry/Hyperbolic/Cusp.lean`), so that this module does not import the admitted declaration
`cusp_constant_sectional_curvature` and can discharge it.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

/-- The cusp curvature formula, for the four fields of a `HyperbolicCusp`. -/
theorem cusp_constant_sectional_curvature_of_fields
    (torusMetric : SmoothRiemannianMetric torusModel Torus)
    (torus_flat : ∀ (p : Torus) (v w : TangentSpace torusModel p),
      metricRm04StandardAt torusMetric p v w w v = 0)
    (metric : SmoothRiemannianMetric halfCollarModel (Torus × EuclideanHalfSpace 1))
    (metric_formula : ∀ (p : Torus × EuclideanHalfSpace 1)
      (v w : TangentSpace halfCollarModel p),
      metric.inner p v w = v.2 0 * w.2 0 +
        Real.exp (-p.2.val 0) * torusMetric.inner p.1 v.1 w.1)
    (p : Torus × EuclideanHalfSpace 1) (v w : TangentSpace halfCollarModel p) :
    metricRm04StandardAt metric p v w w v =
      -(1 / 4 : ℝ) * (metric.inner p v v * metric.inner p w w -
        metric.inner p v w ^ 2) := by
  have hmetric : metric = torusMetric.exponentialWarpedEnd (1 / 2) := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v' w'
    rw [metric_formula, SmoothRiemannianMetric.exponentialWarpedEnd_inner]
    norm_num
  subst hmetric
  rw [metricRm04StandardAt_exponentialWarpedEnd_sectional]
  erw [torus_flat]
  norm_num

end DifferentialGeometry.Geometry.Hyperbolic
