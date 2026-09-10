import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped ENNReal Manifold ContDiff Topology

namespace Poincare.Toponogov

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def riemannianDistance (g : SmoothRiemannianMetric I M) (x y : M) : ℝ :=
  (riemannianEDistOf (I := I) g x y).toReal

def riemannianComparisonAngle (g : SmoothRiemannianMetric I M)
    (x o y : M) : ℝ :=
  comparisonAngle (riemannianDistance (I := I) g o x)
    (riemannianDistance (I := I) g o y)
    (riemannianDistance (I := I) g x y)

theorem riemannianDistance_scale_sq (g : SmoothRiemannianMetric I M)
    {scale : ℝ} (hscale : 0 < scale) (x y : M) :
    riemannianDistance (I := I)
        (scaleMetric (I := I) (scale ^ 2) (sq_pos_of_pos hscale) g) x y =
      scale * riemannianDistance (I := I) g x y := by
  unfold riemannianDistance
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg (scale ^ 2)),
    Real.sqrt_sq hscale.le]

theorem riemannianComparisonAngle_scale_sq
    (g : SmoothRiemannianMetric I M) {scale : ℝ} (hscale : 0 < scale)
    {x o y : M}
    (hox : 0 < riemannianDistance (I := I) g o x)
    (hoy : 0 < riemannianDistance (I := I) g o y) :
    riemannianComparisonAngle (I := I)
        (scaleMetric (I := I) (scale ^ 2) (sq_pos_of_pos hscale) g) x o y =
      riemannianComparisonAngle (I := I) g x o y := by
  unfold riemannianComparisonAngle
  rw [riemannianDistance_scale_sq (I := I) g hscale o x,
    riemannianDistance_scale_sq (I := I) g hscale o y,
    riemannianDistance_scale_sq (I := I) g hscale x y]
  exact comparisonAngle_scale hox hoy hscale

end Poincare.Toponogov
