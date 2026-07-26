import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

/-!
# Elementary L² integral identities

This file records the real-valued conversion between the `eLpNorm` convention
used by measure theory and the ordinary integral of a square.
-/

namespace DifferentialGeometry.Analysis.Integration

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For a real-valued `L²` function, its squared `eLpNorm` is the integral of
its pointwise square. -/
theorem integral_sq_eq_l2 {v : α → ℝ} (hv : MemLp v 2 μ) :
    (∫ x, v x ^ 2 ∂μ) = (eLpNorm v 2 μ).toReal ^ 2 := by
  have h_sq_lintegral :
      (eLpNorm v 2 μ) ^ 2 = ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by rfl
    rw [h2]
    have h_inner_eq : ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
        ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have h_point : ∀ x : α,
      (‖v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (v x ^ 2) := by
    intro x
    rw [← Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [show v x ^ 2 = v x * v x by ring, enorm_mul]
    rw [show (‖v x‖ₑ : ℝ≥0∞) ^ 2 = ‖v x‖ₑ * ‖v x‖ₑ by ring]
  have h_sq_int : Integrable (fun x => v x ^ 2) μ := hv.integrable_sq
  have h_sq_nonneg : 0 ≤ᵐ[μ] fun x => v x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have h_sq :
      (eLpNorm v 2 μ) ^ 2 = ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) := by
    rw [h_sq_lintegral, lintegral_congr fun x => h_point x]
    exact (ofReal_integral_eq_lintegral_ofReal h_sq_int h_sq_nonneg).symm
  have h_int_nonneg : 0 ≤ ∫ x, v x ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have h_toReal :
      ((eLpNorm v 2 μ) ^ 2).toReal = (eLpNorm v 2 μ).toReal ^ 2 :=
    ENNReal.toReal_pow _ 2
  rw [h_sq, ENNReal.toReal_ofReal h_int_nonneg] at h_toReal
  exact h_toReal

end

end DifferentialGeometry.Analysis.Integration
