import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.CosineInverseEstimate

set_option autoImplicit false

open scoped InnerProductSpace

namespace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_add_le_sqrt_of_inner_le {u v : E} {ε : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : ⟪u, v⟫_ℝ ≤ -1 + ε) :
    ‖u + v‖ ≤ Real.sqrt (2 * ε) := by
  have hsq := norm_add_sq_real u v
  rw [hu, hv] at hsq
  exact (Real.le_sqrt (norm_nonneg _) (by nlinarith [sq_nonneg ‖u + v‖])).mpr (by nlinarith)

theorem abs_inner_sub_le_of_almost_antipodal {u v w : E} {t ε : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : ⟪u, v⟫_ℝ ≤ -1 + ε)
    (huw : ⟪u, w⟫_ℝ ≤ t + ε) (hvw : ⟪v, w⟫_ℝ ≤ -t + ε) :
    |⟪u, w⟫_ℝ - t| ≤ ε + Real.sqrt (2 * ε) := by
  have hn := norm_add_le_sqrt_of_inner_le hu hv huv
  have hc := abs_real_inner_le_norm (u + v) w
  rw [hw, mul_one, inner_add_left] at hc
  have hl := (abs_le.mp (hc.trans hn)).1
  exact abs_le.mpr ⟨by linarith, by linarith [Real.sqrt_nonneg (2 * ε)]⟩

theorem norm_sub_le_of_common_almost_antipode {u u' v : E} {ε : ℝ}
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ ≤ -1 + ε) (huv' : ⟪u', v⟫_ℝ ≤ -1 + ε) :
    ‖u - u'‖ ≤ 2 * Real.sqrt (2 * ε) := by
  have h := norm_sub_le (u + v) (u' + v)
  rw [add_sub_add_right_eq_sub] at h
  linarith [norm_add_le_sqrt_of_inner_le hu hv huv,
    norm_add_le_sqrt_of_inner_le hu' hv huv']

theorem angle_le_of_common_almost_antipode {u u' v : E} {ε : ℝ}
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ ≤ -1 + ε) (huv' : ⟪u', v⟫_ℝ ≤ -1 + ε) :
    angle u u' ≤ Real.pi * Real.sqrt (2 * ε) := by
  have hnorm := norm_sub_le_of_common_almost_antipode hu hu' hv huv huv'
  have hc : |⟪u, v⟫_ℝ| ≤ 1 := by simpa only [hu, hv, one_mul] using abs_real_inner_le_norm u v
  have hε : 0 ≤ 2 * ε := by linarith [(abs_le.mp hc).1]
  have hs := Real.sq_sqrt hε
  have hsq := norm_sub_sq_real u u'
  rw [hu, hu'] at hsq
  have hbound : |Real.cos (angle u u') - Real.cos 0| ≤ 2 * (2 * ε) := by
    rw [cos_angle, hu, hu', one_mul, div_one, Real.cos_zero]
    have hi : ⟪u, u'⟫_ℝ ≤ 1 := by simpa only [hu, hu', one_mul] using real_inner_le_norm u u'
    rw [abs_of_nonpos (by linarith : ⟪u, u'⟫_ℝ - 1 ≤ 0)]
    have hh := (sq_le_sq₀ (norm_nonneg (u - u')) (by positivity)).mpr hnorm
    nlinarith
  have h := Real.abs_sub_le_pi_mul_sqrt_of_abs_cos_sub_le
    ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨le_refl 0, Real.pi_pos.le⟩ hbound
  simpa only [sub_zero, abs_of_nonneg (angle_nonneg _ _)] using h

end InnerProductGeometry
