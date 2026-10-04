import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! ZSP01 (master207B, B:6323): actual zero-block isolation and a global fixed-radius error.
(ZL): the reference radius of every contributor beats `20 R_i / T₀`, so the zero support cannot
meet that reference ball (SGP01/EGP02/TCP01 would give `R_i / R_a ≥ T₀/20`).
(ZE): exact equality of the whole zero block where `ρ > 200 R_i/T₀` and the relative error
`|f - F| < c₃ ρ` give the global error `200 c₃ R_i / T₀`, also on the segment `F → E`. -/

set_option autoImplicit false
open Set

namespace GC.MetricGeometry

theorem zero_reference_scale_contradiction {ρ Ri Ra T₀ : ℝ} (hT : 0 < T₀) (hRi : 0 < Ri)
    (hρ : 200 * Ri / T₀ < ρ) (hRa : 108 / 625 * ρ ≤ Ra) :
    20 * Ri / T₀ < Ra ∧ Ri / Ra < T₀ / 20 := by
  have h1 : 20 * Ri / T₀ < 108 / 625 * (200 * Ri / T₀) := by
    have : 0 < Ri / T₀ := div_pos hRi hT
    rw [mul_div_assoc, mul_div_assoc]
    nlinarith
  have hlt : 20 * Ri / T₀ < Ra := by nlinarith
  refine ⟨hlt, ?_⟩
  have hRa0 : 0 < Ra := lt_trans (by positivity) hlt
  rw [div_lt_div_iff₀ hRa0 (by norm_num)]
  rw [div_lt_iff₀ hT] at hlt
  linarith

variable {M H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_zero_block_sub_lt (f F : M → H) (J : H →L[ℝ] V) (hJ : ‖J‖ ≤ 1) (ρ : M → ℝ)
    {R T₀ c₃ : ℝ} (hR : 0 < R) (hT : 0 < T₀) (hc₃ : 0 < c₃)
    (hZI : ∀ p, 200 * R / T₀ < ρ p → J (f p) = J (F p))
    (herr : ∀ p, ‖f p - F p‖ < c₃ * ρ p) :
    ∀ p, ‖J (f p - F p)‖ < 200 * c₃ / T₀ * R := by
  intro p
  have hpos : 0 < 200 * c₃ / T₀ * R := by positivity
  by_cases h : 200 * R / T₀ < ρ p
  · rw [map_sub, hZI p h, sub_self, norm_zero]
    exact hpos
  · have hle : ρ p ≤ 200 * R / T₀ := le_of_not_gt h
    have h1 : ‖J (f p - F p)‖ ≤ ‖f p - F p‖ :=
      (J.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hJ)
    have h2 : c₃ * ρ p ≤ c₃ * (200 * R / T₀) := mul_le_mul_of_nonneg_left hle hc₃.le
    have h3 : c₃ * (200 * R / T₀) = 200 * c₃ / T₀ * R := by ring
    linarith [herr p]

theorem norm_zero_block_segment_sub_lt (F E : M → H) (J : H →L[ℝ] V) (hJ : ‖J‖ ≤ 1)
    (ρ : M → ℝ) {R T₀ c₃ : ℝ} (hR : 0 < R) (hT : 0 < T₀) (hc₃ : 0 < c₃)
    (hZI : ∀ p, 200 * R / T₀ < ρ p → J (E p) = J (F p))
    (herr : ∀ p, ‖E p - F p‖ < c₃ * ρ p) :
    ∀ p, ∀ τ ∈ Icc (0 : ℝ) 1, ‖J (((1 - τ) • F p + τ • E p) - F p)‖ < 200 * c₃ / T₀ * R := by
  intro p τ hτ
  have h := norm_zero_block_sub_lt E F J hJ ρ hR hT hc₃ hZI herr p
  have heq : ((1 - τ) • F p + τ • E p) - F p = τ • (E p - F p) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [heq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  calc τ * ‖J (E p - F p)‖ ≤ ‖J (E p - F p)‖ := mul_le_of_le_one_left (norm_nonneg _) hτ.2
    _ < _ := h

theorem zero_error_le_and_lt {c₃ T₀ : ℝ} (hT : 200 ≤ T₀) (hc₃ : 0 ≤ c₃) (hc : c₃ < 1 / 1000) :
    200 * c₃ / T₀ ≤ c₃ ∧ 200 * c₃ / T₀ < 1 / 1000 := by
  have hT0 : 0 < T₀ := by linarith
  have h : 200 * c₃ / T₀ ≤ c₃ := by
    rw [div_le_iff₀ hT0]
    nlinarith
  exact ⟨h, lt_of_le_of_lt h hc⟩

end GC.MetricGeometry
