import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section

open scoped InnerProductSpace ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialBilinearForm (e : E) (c : ℝ) : E →L[ℝ] E →L[ℝ] ℝ := by
  let b : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  exact c • b + (1 - c) • (innerSL ℝ e).smulRight (innerSL ℝ e)

theorem radialBilinearForm_apply (e v w : E) (c : ℝ) :
    radialBilinearForm e c v w =
      c * ⟪v, w⟫_ℝ + (1 - c) * ⟪e, v⟫_ℝ * ⟪e, w⟫_ℝ := by
  change c * ⟪v, w⟫_ℝ + (1 - c) * (⟪e, v⟫_ℝ * ⟪e, w⟫_ℝ) = _
  ring

theorem radialBilinearForm_symm (e v w : E) (c : ℝ) :
    radialBilinearForm e c v w = radialBilinearForm e c w v := by
  simp only [radialBilinearForm_apply, real_inner_comm v w]
  ring

theorem radialBilinearForm_radial {e : E} (he : ‖e‖ = 1) (c : ℝ) (v : E) :
    radialBilinearForm e c e v = ⟪e, v⟫_ℝ := by
  rw [radialBilinearForm_apply, real_inner_self_eq_norm_sq, he]
  ring

theorem radialBilinearForm_tangential (e w : E) {v : E}
    (hv : ⟪e, v⟫_ℝ = 0) (c : ℝ) :
    radialBilinearForm e c v w = c * ⟪v, w⟫_ℝ := by
  simp [radialBilinearForm_apply, hv]

theorem radialBilinearForm_lower_bound {e : E} (he : ‖e‖ = 1)
    (c : ℝ) (v : E) :
    min c 1 * ‖v‖ ^ 2 ≤ radialBilinearForm e c v v := by
  rw [radialBilinearForm_apply, real_inner_self_eq_norm_sq]
  have hinner : ⟪e, v⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := real_inner_mul_inner_self_le e v
    simpa [real_inner_self_eq_norm_sq, he, pow_two] using h
  rcases le_total c 1 with hc | hc
  · rw [min_eq_left hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg ⟪e, v⟫_ℝ)]
  · rw [min_eq_right hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (sub_nonneg.mpr hinner)]

theorem radialBilinearForm_pos {e : E} (he : ‖e‖ = 1)
    {c : ℝ} (hc : 0 < c) {v : E} (hv : v ≠ 0) :
    0 < radialBilinearForm e c v v := by
  exact lt_of_lt_of_le
    (mul_pos (lt_min hc zero_lt_one) (sq_pos_of_pos (norm_pos_iff.mpr hv)))
    (radialBilinearForm_lower_bound he c v)

theorem radialBilinearForm_upper_bound {e : E} (he : ‖e‖ = 1)
    (c : ℝ) (v : E) :
    radialBilinearForm e c v v ≤ max c 1 * ‖v‖ ^ 2 := by
  rw [radialBilinearForm_apply, real_inner_self_eq_norm_sq]
  have hinner : ⟪e, v⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa [real_inner_self_eq_norm_sq, he, pow_two] using
      real_inner_mul_inner_self_le e v
  rcases le_total c 1 with hc | hc
  · rw [max_eq_right hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hinner)]
  · rw [max_eq_left hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg ⟪e, v⟫_ℝ)]

theorem inner_sq_le_radialBilinearForm {e : E} (he : ‖e‖ = 1)
    {c : ℝ} (hc : 0 ≤ c) (v : E) :
    ⟪e, v⟫_ℝ ^ 2 ≤ radialBilinearForm e c v v := by
  rw [radialBilinearForm_apply, real_inner_self_eq_norm_sq]
  have hinner : ⟪e, v⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa [real_inner_self_eq_norm_sq, he, pow_two] using
      real_inner_mul_inner_self_le e v
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hinner)]

theorem radialBilinearForm_linearIsometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F)
    (e v w : E) (c : ℝ) :
    radialBilinearForm (f e) c (f v) (f w) = radialBilinearForm e c v w := by
  simp only [radialBilinearForm_apply, f.inner_map_map]

theorem radialBilinearForm_polar {e : E} (he : ‖e‖ = 1)
    {v w : E} (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0)
    {r : ℝ} (hr : r ≠ 0) (a s t : ℝ) :
    radialBilinearForm e ((a / r) ^ 2) (s • e + r • v) (t • e + r • w) =
      s * t + a ^ 2 * ⟪v, w⟫_ℝ := by
  have hve : ⟪v, e⟫_ℝ = 0 := by rw [real_inner_comm, hv]
  simp only [radialBilinearForm_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    he, hv, hw, hve]
  field_simp
  ring

end DifferentialGeometry.Geometry.Riemannian
