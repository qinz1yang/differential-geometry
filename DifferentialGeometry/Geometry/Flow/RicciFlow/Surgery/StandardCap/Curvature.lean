import DifferentialGeometry.Geometry.Metric.RadialCurvature
import DifferentialGeometry.Geometry.Curvature.Nonnegative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.TipCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ProfileEstimates

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian
open scoped Manifold InnerProductSpace Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem metric_eventually_radial {x : E3} (hx : x ≠ 0) :
    (fun y => tangentBilinearFormToModel y (metric.inner y)) =ᶠ[𝓝 x]
      radialBilinearField warpingFunction := by
  filter_upwards [eventually_ne_nhds hx] with y hy
  ext u v
  exact metric_inner_of_ne_zero hy u v

theorem metricRm04_radial {x v : E3} (hx : x ≠ 0) (hv : ⟪x, v⟫_ℝ = 0) :
    metricRm04StandardAt metric x x v v x =
      -warpingFunction ‖x‖ * deriv (deriv warpingFunction) ‖x‖ * ‖v‖ ^ 2 := by
  exact metricRm04StdAt_radialBilinearField_radial metric (metric_eventually_radial hx)
    contDiff_warpingFunction hx (warpingFunction_pos (norm_pos_iff.mpr hx)).ne' hv

theorem metricRm04_tangential {x v w : E3} (hx : x ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0) :
    metricRm04StandardAt metric x v w w v =
      warpingFunction ‖x‖ ^ 2 * (1 - deriv warpingFunction ‖x‖ ^ 2) / ‖x‖ ^ 4 *
        (‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2) := by
  exact metricRm04StdAt_radialBilinearField_tangential metric (metric_eventually_radial hx)
    contDiff_warpingFunction hx (warpingFunction_pos (norm_pos_iff.mpr hx)).ne' hv hw

theorem metric_inner_tangential {x v : E3} (hx : x ≠ 0) (hv : ⟪x, v⟫_ℝ = 0) (w : E3) :
    metric.inner x v w = (warpingFunction ‖x‖ / ‖x‖) ^ 2 * ⟪v, w⟫_ℝ :=
  (metric_inner_of_ne_zero hx v w).trans (radialBilinearField_tangential _ x w hv)

theorem sectionalCurvature_radial {x v : E3} (hx : x ≠ 0)
    (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    sectionalCurvature metric x x v = -deriv (deriv warpingFunction) ‖x‖ / warpingFunction ‖x‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have ha : warpingFunction ‖x‖ ≠ 0 := (warpingFunction_pos (norm_pos_iff.mpr hx)).ne'
  calc
    _ = metricRm04StandardAt metric x x v v x /
        (metric.inner x x x * metric.inner x v v - (metric.inner x x v) ^ 2) :=
      sectionalCurvature_eq_metricRm04StandardAt_div metric x x v
    _ = _ := by
      rw [metricRm04_radial hx hxv, metric_inner_radial, metric_inner_radial,
        metric_inner_tangential hx hxv, hxv, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      field_simp
      ring

theorem sectionalCurvature_tangential {x v w : E3} (hx : x ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0)
    (hvw : ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 ≠ 0) :
    sectionalCurvature metric x v w =
      (1 - deriv warpingFunction ‖x‖ ^ 2) / warpingFunction ‖x‖ ^ 2 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ha : warpingFunction ‖x‖ ≠ 0 := (warpingFunction_pos (norm_pos_iff.mpr hx)).ne'
  calc
    _ = metricRm04StandardAt metric x v w w v /
        (metric.inner x v v * metric.inner x w w - (metric.inner x v w) ^ 2) :=
      sectionalCurvature_eq_metricRm04StandardAt_div metric x v w
    _ = _ := by
      rw [metricRm04_tangential hx hv hw, metric_inner_tangential hx hv,
        metric_inner_tangential hx hw, metric_inner_tangential hx hv,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have hg : (warpingFunction ‖x‖ / ‖x‖) ^ 2 * ‖v‖ ^ 2 *
          ((warpingFunction ‖x‖ / ‖x‖) ^ 2 * ‖w‖ ^ 2) -
          ((warpingFunction ‖x‖ / ‖x‖) ^ 2 * ⟪v, w⟫_ℝ) ^ 2 =
          (warpingFunction ‖x‖ / ‖x‖) ^ 4 * (‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2) := by ring
      rw [hg]
      field_simp

theorem sectionalCurvature_radial_nonneg {x v : E3} (hx : x ≠ 0)
    (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    0 ≤ sectionalCurvature metric x x v := by
  rw [sectionalCurvature_radial hx hv hxv]
  exact neg_deriv_deriv_warpingFunction_div_nonneg (norm_pos_iff.mpr hx)

theorem half_le_sectionalCurvature_tangential {x v w : E3} (hx : x ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0)
    (hvw : ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 ≠ 0) :
    1 / 2 ≤ sectionalCurvature metric x v w := by
  rw [sectionalCurvature_tangential hx hv hw hvw]
  exact half_le_one_sub_deriv_warpingFunction_sq_div (norm_pos_iff.mpr hx)

theorem sectionalCurvature_radial_cylindrical {x v : E3}
    (hx : transitionEnd ≤ ‖x‖) (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    sectionalCurvature metric x x v = 0 :=
  (sectionalCurvature_radial (norm_pos_iff.mp (transitionEnd_pos.trans_le hx)) hv hxv).trans
    (neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le hx)

theorem sectionalCurvature_tangential_cylindrical {x v w : E3}
    (hx : transitionEnd ≤ ‖x‖) (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0)
    (hvw : ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 ≠ 0) :
    sectionalCurvature metric x v w = 1 / 2 :=
  (sectionalCurvature_tangential (norm_pos_iff.mp (transitionEnd_pos.trans_le hx)) hv hw hvw).trans
    (one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le hx)

theorem sectionalCurvature_radial_eq_angle {x v : E3} (hx : x ≠ 0)
    (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    sectionalCurvature metric x x v = (deriv angle ‖x‖) ^ 2 -
      Real.cot (angle ‖x‖) * deriv (deriv angle) ‖x‖ :=
  (sectionalCurvature_radial hx hv hxv).trans
    (neg_deriv_deriv_warpingFunction_div_eq_angle (norm_pos_iff.mpr hx))

theorem sectionalCurvature_tangential_eq_angle {x v w : E3} (hx : x ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0)
    (hvw : ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 ≠ 0) :
    sectionalCurvature metric x v w =
      (1 - 2 * (Real.cos (angle ‖x‖)) ^ 2 * (deriv angle ‖x‖) ^ 2) /
        (2 * (Real.sin (angle ‖x‖)) ^ 2) :=
  (sectionalCurvature_tangential hx hv hw hvw).trans
    (one_sub_deriv_warpingFunction_sq_div_eq_angle ‖x‖)

theorem metricRm04_nonneg (x u v : E3) : 0 ≤ metricRm04StandardAt metric x u v v u := by
  by_cases hx : x = 0
  · subst x
    rw [metricRm04_zero]
    apply mul_nonneg (by norm_num)
    simpa only [← pow_two, sub_nonneg] using real_inner_mul_inner_self_le u v
  · have hslope : |deriv warpingFunction ‖x‖| ≤ 1 := by
      rw [abs_of_nonneg (deriv_warpingFunction_nonneg (norm_nonneg x))]
      exact deriv_warpingFunction_le_one ‖x‖
    exact metricRm04StdAt_radialBilinearField_nonneg metric (metric_eventually_radial hx)
      contDiff_warpingFunction hx (warpingFunction_pos (norm_pos_iff.mpr hx))
      (deriv_deriv_warpingFunction_nonpos (norm_nonneg x)) hslope u v

theorem hasNonnegativeSectionalCurvature_metric :
    DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature metric :=
  (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff metric).mpr metricRm04_nonneg

theorem sectionalCurvature_nonneg (x u v : E3) : 0 ≤ sectionalCurvature metric x u v := by
  have hd : 0 ≤ metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2 :=
    sectionalCurvatureDenominator_nonneg metric x u v
  exact (div_nonneg (metricRm04_nonneg x u v) hd).trans_eq
    (sectionalCurvature_eq_metricRm04StandardAt_div metric x u v).symm

end DifferentialGeometry.PDE.RicciFlow.StandardCap
