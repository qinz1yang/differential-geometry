import DifferentialGeometry.Analysis.InnerProductSpace.AsymmetricTestSaturation

/-!
# Consumer of the pointwise asymmetric tests (EGP04)

On the real line, the identity covector and `(999/1000)·id` pass two derivative tests along the unit
direction `1` with segment length `400` (EGP04's `400 Δ` with `Δ = 1`), quality `1/1000` and gain
defect `1`; the FC22 scalar step produces the second gain from a long gain of `10⁴` and an
intermediate point at distance `400`.
-/

set_option autoImplicit false

namespace ContinuousLinearMap

theorem asymmetric_tests_real_line_example :
    ‖ContinuousLinearMap.id ℝ ℝ - (999 / 1000 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ ≤
      2 * Real.sqrt (4 * (1 / 1000 + 1 / 400) + (1 / 1000 + 1 / 400) ^ 2) := by
  have hshort : (400 : ℝ) - (1 / 2 + 1 / 4 + 2 * (1 / 8)) ≤ 400 - 0 :=
    short_gain_of_long_tests (Ψx := 0) (Ψy := 10000) (Ψz := 400) (Ux := 0) (Uz := 400) (b := 0)
      (ℓ := 10000) (t := 400) (β := 1 / 2) (δ := 1 / 4) (E := 1 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply norm_sub_le_of_asymmetric_tests (ContinuousLinearMap.id ℝ ℝ)
    ((999 / 1000 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 (by simp) (ς := 1 / 1000) (e := 1)
    (ℓ₀ := 400) (ℓ₁ := 400) (ℓ₂ := 400) (G₁ := 400) (G₂ := 3996 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  · rw [norm_id]; norm_num
  · rw [norm_smul, norm_id]; norm_num
  · exact le_rfl
  · exact le_rfl
  · simp
  · linarith
  · simp only [smul_apply, id_apply, smul_eq_mul]; norm_num
  · norm_num

end ContinuousLinearMap

theorem affine_value_error_example :
    |2 * (1 : ℝ) - (-1 * (-1) + 1)| ≤ 2 * (1 / 10) + 1 / 5 + 1 / 10 :=
  abs_affine_value_error_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (show |2 * (1 : ℝ) - -1 * (-1) - 1| ≤ 1 / 5 by norm_num)
