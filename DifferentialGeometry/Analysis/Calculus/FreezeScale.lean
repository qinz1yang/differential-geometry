import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem scalar_weight_c1_perturbation_le {σ : E → ℝ} {F : E → H} {x : E}
    (hσ : DifferentiableAt ℝ σ x) (hF : DifferentiableAt ℝ F x) {ε δ M A : ℝ}
    (hclose : |σ x - 1| ≤ ε) (hDσ : ‖fderiv ℝ σ x‖ ≤ δ)
    (hvalue : ‖F x‖ ≤ M) (hDF : ‖fderiv ℝ F x‖ ≤ A) :
    max ‖σ x • F x - F x‖ ‖fderiv ℝ (fun y => σ y • F y) x - fderiv ℝ F x‖ ≤
      (ε + δ) * M + ε * A := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hclose
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hDσ
  have hM : 0 ≤ M := (norm_nonneg _).trans hvalue
  have hA : 0 ≤ A := (norm_nonneg _).trans hDF
  have hv : ‖σ x • F x - F x‖ ≤ ε * M := by
    have heq : (σ x - 1) • F x = σ x • F x - F x := by rw [sub_smul, one_smul]
    rw [← heq, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hclose hvalue (norm_nonneg _) hε
  have hd := hσ.hasFDerivAt.smul hF.hasFDerivAt
  have hsplit : σ x • fderiv ℝ F x + (fderiv ℝ σ x).smulRight (F x) - fderiv ℝ F x =
      (σ x - 1) • fderiv ℝ F x + (fderiv ℝ σ x).smulRight (F x) := by module
  have hderiv : ‖fderiv ℝ (fun y => σ y • F y) x - fderiv ℝ F x‖ ≤ ε * A + δ * M := by
    change ‖fderiv ℝ (σ • F) x - fderiv ℝ F x‖ ≤ _
    rw [hd.fderiv, hsplit]
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
    exact add_le_add (mul_le_mul hclose hDF (norm_nonneg _) hε)
      (mul_le_mul hDσ hvalue (norm_nonneg _) hδ)
  apply max_le
  · nlinarith [mul_nonneg hδ hM, mul_nonneg hε hA]
  · nlinarith [mul_nonneg hε hM]

theorem freeze_scale_product_c1_le {σ : E → ℝ} {F : E → H} {x : E}
    (hσ : DifferentiableAt ℝ σ x) (hF : DifferentiableAt ℝ F x) {L Λ V Δ A : ℝ}
    (hclose : |σ x - 1| ≤ L * Λ) (hDσ : ‖fderiv ℝ σ x‖ ≤ Λ)
    (hvalue : ‖F x‖ ≤ V * Δ) (hDF : ‖fderiv ℝ F x‖ ≤ A) :
    max ‖σ x • F x - F x‖ ‖fderiv ℝ (fun y => σ y • F y) x - fderiv ℝ F x‖ ≤
      Λ * ((L + 1) * V * Δ + L * A) :=
  (scalar_weight_c1_perturbation_le hσ hF hclose hDσ hvalue hDF).trans_eq (by ring)

theorem freeze_scale_quotient_c1_le {σ u : E → ℝ} {x : E}
    (hσ : DifferentiableAt ℝ σ x) (hu : DifferentiableAt ℝ u x) {L Λ C Δ D₁ : ℝ}
    (hsmall : L * Λ ≤ 1 / 2) (hclose : |σ x - 1| ≤ L * Λ)
    (hDσ : ‖fderiv ℝ σ x‖ ≤ Λ) (hvalue : |u x| ≤ C * Δ) (hDu : ‖fderiv ℝ u x‖ ≤ D₁) :
    max |u x / σ x - u x| ‖fderiv ℝ (fun y => u y / σ y) x - fderiv ℝ u x‖ ≤
      Λ * ((2 * L + 4) * C * Δ + 2 * L * D₁) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hDσ
  have hs : (1 / 2 : ℝ) ≤ σ x := by linarith [(abs_le.mp hclose).1]
  have hs0 : 0 < σ x := by linarith
  have hi : (σ x)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hs0).mpr
    linarith
  have hiclose : |(σ x)⁻¹ - 1| ≤ 2 * L * Λ := by
    have heq : (σ x)⁻¹ - 1 = (1 - σ x) * (σ x)⁻¹ := by field_simp
    rw [heq, abs_mul, abs_sub_comm 1, abs_of_pos (inv_pos.mpr hs0)]
    have hm := mul_le_mul hclose hi (inv_nonneg.mpr hs0.le)
      ((abs_nonneg _).trans hclose)
    nlinarith
  have hinv := (hasDerivAt_inv hs0.ne').comp_hasFDerivAt x hσ.hasFDerivAt
  have hiD : ‖fderiv ℝ (fun y => (σ y)⁻¹) x‖ ≤ 4 * Λ := by
    change ‖fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ σ) x‖ ≤ _
    rw [hinv.fderiv, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_pow,
      abs_of_pos hs0, ← inv_pow]
    have hsquare : (σ x)⁻¹ ^ 2 ≤ 4 := by nlinarith [inv_nonneg.mpr hs0.le]
    exact mul_le_mul hsquare hDσ (norm_nonneg _) (by norm_num)
  have hb := scalar_weight_c1_perturbation_le hinv.differentiableAt hu hiclose hiD
    (by simpa only [Real.norm_eq_abs] using hvalue) hDu
  have heq : (2 * L * Λ + 4 * Λ) * (C * Δ) + 2 * L * Λ * D₁ =
      Λ * ((2 * L + 4) * C * Δ + 2 * L * D₁) := by ring
  rw [heq] at hb
  simpa only [Function.comp_apply, smul_eq_mul, mul_comm, ← div_eq_mul_inv, Real.norm_eq_abs] using hb

end DifferentialGeometry.Analysis
