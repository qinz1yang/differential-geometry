import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Curvature
import DifferentialGeometry.Geometry.Curvature.RadialOperator

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold InnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem metric_curvatureOperator_nonnegative (x : E3) :
    metricAlgebraicCurvatureTensorAt metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := 𝓡 3) (M := E3) := by
  by_cases hx : x = 0
  · subst x
    apply metricAlgebraicCurvatureTensorAt_nonnegative_of_constant_sectional_numerator
      metric 0 (K := 1 / 2) (by norm_num)
    intro u v
    have hinner (p q : TangentSpace (𝓡 3) (0 : E3)) :
        metric.inner 0 p q = ⟪(show E3 from p), (show E3 from q)⟫_ℝ := metric_inner_zero p q
    rw [hinner, hinner, hinner]
    exact metricRm04_zero u v
  · have hslope : |deriv warpingFunction ‖x‖| ≤ 1 := by
      rw [abs_of_nonneg (deriv_warpingFunction_nonneg (norm_nonneg x))]
      exact deriv_warpingFunction_le_one ‖x‖
    exact metricAlgebraicCurvatureTensorAt_radialBilinearField_nonnegative metric
      (metric_eventually_radial hx) contDiff_warpingFunction hx
      (warpingFunction_pos (norm_pos_iff.mpr hx))
      (deriv_deriv_warpingFunction_nonpos (norm_nonneg x)) hslope

end DifferentialGeometry.PDE.RicciFlow.StandardCap
