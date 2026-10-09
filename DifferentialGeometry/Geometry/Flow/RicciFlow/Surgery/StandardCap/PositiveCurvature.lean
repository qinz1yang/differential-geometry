import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CurvatureProfiles
import DifferentialGeometry.Geometry.Curvature.RadialPositive

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian
open scoped Manifold InnerProductSpace ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem deriv_angle_pos {r : ℝ} (hr : r < transitionEnd) : 0 < deriv angle r := by
  rw [deriv_angle]
  exact mul_pos (by positivity) (Real.smoothTransition.pos_of_pos (sub_pos.mpr hr))

theorem deriv_deriv_warpingFunction_neg {r : ℝ} (hr : 0 < r) (hL : r < transitionEnd) :
    deriv (deriv warpingFunction) r < 0 := by
  rw [deriv_deriv_warpingFunction]
  apply mul_neg_of_pos_of_neg (by positivity)
  have hcos : 0 ≤ Real.cos (angle r) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg hr.le, Real.pi_pos],
      angle_le_pi_div_two r⟩
  have hsin : 0 < Real.sin (angle r) :=
    Real.sin_pos_of_pos_of_lt_pi (angle_pos hr)
      ((angle_le_pi_div_two r).trans_lt (half_lt_self Real.pi_pos))
  exact sub_neg.mpr ((mul_nonpos_of_nonneg_of_nonpos hcos
    (deriv_deriv_angle_nonpos r)).trans_lt (mul_pos hsin (sq_pos_of_pos (deriv_angle_pos hL))))

theorem abs_deriv_warpingFunction_lt_one {r : ℝ} (hr : 0 < r) :
    |deriv warpingFunction r| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have ha := sq_pos_of_pos (warpingFunction_pos hr)
  linarith [deriv_warpingFunction_sq_add_half_sq_le_one r]

theorem radialSectionalValue_pos {r : ℝ} (hr : r < transitionEnd) :
    0 < radialSectionalValue r := by
  by_cases h0 : r ≤ 0
  · norm_num [radialSectionalValue, h0]
  · have hp : 0 < r := lt_of_not_ge h0
    rw [radialSectionalValue_of_pos hp]
    exact div_pos (neg_pos.mpr (deriv_deriv_warpingFunction_neg hp hr)) (warpingFunction_pos hp)

theorem sectionalCurvature_radial_pos {x v : E3} (hx : x ≠ 0)
    (hL : ‖x‖ < transitionEnd) (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    0 < sectionalCurvature metric x x v := by
  rw [sectionalCurvature_radial_eq_profile hx hv hxv]
  exact radialSectionalValue_pos hL

theorem metricRm04_pos {x : E3} (hL : ‖x‖ < transitionEnd) (u v : E3)
    (hplane : 0 < metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2) :
    0 < metricRm04StandardAt metric x u v v u := by
  by_cases hx : x = 0
  · subst x
    rw [metricRm04_zero]
    apply mul_pos (by norm_num)
    simpa only [metric_inner_zero] using hplane
  · exact metricRm04StdAt_radialBilinearField_pos metric (metric_eventually_radial hx)
      contDiff_warpingFunction hx (warpingFunction_pos (norm_pos_iff.mpr hx))
      (deriv_deriv_warpingFunction_neg (norm_pos_iff.mpr hx) hL)
      (abs_deriv_warpingFunction_lt_one (norm_pos_iff.mpr hx)) u v hplane

theorem sectionalCurvature_pos {x : E3} (hL : ‖x‖ < transitionEnd) (u v : E3)
    (hplane : metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2 ≠ 0) :
    0 < sectionalCurvature metric x u v := by
  have hpos : 0 < metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2 :=
    (sectionalCurvatureDenominator_nonneg metric x u v).lt_of_ne' hplane
  exact (div_pos (metricRm04_pos hL u v hpos) hpos).trans_eq
    (sectionalCurvature_eq_metricRm04StandardAt_div metric x u v).symm

end DifferentialGeometry.PDE.RicciFlow.StandardCap
