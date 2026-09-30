import DifferentialGeometry.Geometry.Metric.EuclideanCone
import DifferentialGeometry.Geometry.Comparison.SphericalModelAngle

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

def secLift (p a : Y) (ha : dist p a < Real.pi / 2) : EuclideanCone Y :=
  mk (NNReal.mk ((Real.cos (dist p a))⁻¹) (inv_nonneg.mpr
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [dist_nonneg (x := p) (y := a),
      Real.pi_pos], ha⟩).le)) a

@[simp] theorem radius_secLift (p a : Y) (ha : dist p a < Real.pi / 2) :
    radius (secLift p a ha) = (Real.cos (dist p a))⁻¹ := by
  simp [secLift]

@[simp] theorem secLift_self (p : Y) :
    secLift p p (by simpa using Real.pi_div_two_pos) = mk 1 p := by
  simp only [secLift, dist_self, Real.cos_zero, inv_one]
  rfl

theorem dist_mk_one_secLift (p a : Y) (ha : dist p a < Real.pi / 2) :
    dist (mk 1 p) (secLift p a ha) = Real.tan (dist p a) := by
  have hc : 0 < Real.cos (dist p a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [dist_nonneg (x := p) (y := a),
      Real.pi_pos], ha⟩
  have hd : dist p a < Real.pi := by linarith [Real.pi_pos]
  have hsq := coneDistance_sq (x := ((1 : ℝ), p))
    (y := ((Real.cos (dist p a))⁻¹, a)) zero_le_one (inv_pos.mpr hc).le
  dsimp only [Prod.fst, Prod.snd] at hsq
  rw [min_eq_right hd.le] at hsq
  have ht : Real.tan (dist p a) ^ 2 = (Real.cos (dist p a))⁻¹ ^ 2 - 1 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (dist p a)]
  have htan : 0 ≤ Real.tan (dist p a) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two dist_nonneg ha.le
  have he : (1 : ℝ) ^ 2 + (Real.cos (dist p a))⁻¹ ^ 2 -
      2 * 1 * (Real.cos (dist p a))⁻¹ * Real.cos (dist p a) =
      (Real.cos (dist p a))⁻¹ ^ 2 - 1 := by
    field_simp
    ring
  rw [he, ← ht] at hsq
  unfold secLift
  rw [dist_mk]
  exact (sq_eq_sq₀ (coneDistance_nonneg _ _) htan).mp hsq

theorem dist_mk_one_secLift_pos {p a : Y} (hpa : 0 < dist p a)
    (ha : dist p a < Real.pi / 2) : 0 < dist (mk 1 p) (secLift p a ha) := by
  rw [dist_mk_one_secLift]
  exact Real.tan_pos_of_pos_of_lt_pi_div_two hpa ha

end Metric.EuclideanCone

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem comparisonAngle_secLift {p a b : Y}
    (hpa : 0 < dist p a) (hpb : 0 < dist p b)
    (ha : dist p a < Real.pi / 2) (hb : dist p b < Real.pi / 2) :
    comparisonAngle (dist (mk 1 p) (secLift p a ha))
      (dist (mk 1 p) (secLift p b hb)) (dist (secLift p a ha) (secLift p b hb)) =
      sphericalComparisonAngle (dist p a) (dist p b) (dist a b) := by
  have hca : 0 < Real.cos (dist p a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha⟩
  have hcb : 0 < Real.cos (dist p b) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb⟩
  have hsa : 0 < Real.sin (dist p a) :=
    Real.sin_pos_of_pos_of_lt_pi hpa (by linarith [Real.pi_pos])
  have hsb : 0 < Real.sin (dist p b) :=
    Real.sin_pos_of_pos_of_lt_pi hpb (by linarith [Real.pi_pos])
  have hab : dist a b < Real.pi := by
    have ht := dist_triangle a p b
    rw [dist_comm a p] at ht
    linarith
  have hsq := coneDistance_sq (x := ((Real.cos (dist p a))⁻¹, a))
    (y := ((Real.cos (dist p b))⁻¹, b))
    (inv_pos.mpr hca).le (inv_pos.mpr hcb).le
  dsimp only [Prod.fst, Prod.snd] at hsq
  rw [min_eq_right hab.le] at hsq
  rw [dist_mk_one_secLift, dist_mk_one_secLift, secLift, secLift, dist_mk,
    comparisonAngle, comparisonCosine]
  simp only [NNReal.coe_mk]
  rw [hsq, sphericalComparisonAngle,
    spherical_comparison_cosine_eq_secant_quotient hca.ne' hcb.ne' hsa.ne' hsb.ne']

end DifferentialGeometry.Geometry.Comparison.Toponogov
