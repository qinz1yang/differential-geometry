import DifferentialGeometry.Geometry.Metric.ConeAntipodalLine
import DifferentialGeometry.Geometry.Comparison.LineDistance

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem lineCoordinate_twoRayPath_mk (a b u : Y) (r : ℝ≥0) :
    lineCoordinate (twoRayPath a b) (mk r u) =
      (r : ℝ) * Real.cos (min Real.pi (dist a u)) := by
  have hone : twoRayPath a b (1 : ℝ) = mk 1 a := twoRayPath_coe a b 1
  have hs : dist (mk r u) (mk 1 a) ^ 2 =
      (r : ℝ) ^ 2 + 1 - 2 * r * Real.cos (min Real.pi (dist a u)) := by
    rw [dist_mk, coneDistance_sq r.property (by norm_num)]
    simp only [NNReal.coe_one, one_pow, mul_one, dist_comm u a]
  rw [lineCoordinate, twoRayPath_zero, dist_tip, radius_mk, hone, hs]
  ring

theorem lineCoordinate_twoRayPath_mk_eq_zero_iff (a b u : Y) {r : ℝ≥0}
    (hr : 0 < (r : ℝ)) :
    lineCoordinate (twoRayPath a b) (mk r u) = 0 ↔ dist a u = Real.pi / 2 := by
  rw [lineCoordinate_twoRayPath_mk]
  constructor
  · intro h
    have hc := (mul_eq_zero.mp h).resolve_left hr.ne'
    have he : min Real.pi (dist a u) = Real.pi / 2 :=
      Real.injOn_cos ⟨le_min Real.pi_pos.le dist_nonneg, min_le_left _ _⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩
        (by rw [hc, Real.cos_pi_div_two])
    by_cases hd : dist a u ≤ Real.pi
    · rwa [min_eq_right hd] at he
    · rw [min_eq_left (le_of_not_ge hd)] at he
      linarith [Real.pi_pos]
  · intro h
    rw [h, min_eq_right (by linarith [Real.pi_pos]), Real.cos_pi_div_two, mul_zero]

end DifferentialGeometry.Geometry.Comparison.Toponogov
