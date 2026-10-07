import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

/-!
# CX-SPINE G1：seed threshold 与 normalized distance 算术

固定 Kb 后 H=max(4,2Kb)；Q0=H/r²、qcan=Q0/2，D=2A√H。
这些是数值恒等式与不等式，不提供 canonical / Claim 2 的几何输入。
-/

namespace GC.LongTime.Ch11

/-- 固定 seed threshold 同时严格高于种子界 3，并支付两倍 Kb。 -/
theorem seed_threshold_constants_CXSP (Kb : ℝ) :
    0 < max 4 (2 * Kb) ∧ 3 < max 4 (2 * Kb) ∧
      Kb ≤ max 4 (2 * Kb) / 2 := by
  have h4 : (4 : ℝ) ≤ max 4 (2 * Kb) := le_max_left _ _
  have hKb : 2 * Kb ≤ max 4 (2 * Kb) := le_max_right _ _
  constructor
  · linarith
  constructor <;> linarith

/-- qcan≤Q0 的严格间隙，以及种子和 (b) 的 lower threshold。 -/
theorem seed_threshold_bounds_CXSP (Kb : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < max 4 (2 * Kb) * (r ^ 2)⁻¹ ∧
      3 * (r ^ 2)⁻¹ < max 4 (2 * Kb) * (r ^ 2)⁻¹ ∧
      Kb * (r ^ 2)⁻¹ ≤ (max 4 (2 * Kb) / 2) * (r ^ 2)⁻¹ ∧
      (max 4 (2 * Kb) / 2) * (r ^ 2)⁻¹ <
        max 4 (2 * Kb) * (r ^ 2)⁻¹ := by
  obtain ⟨hH, h3, hKb⟩ := seed_threshold_constants_CXSP Kb
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  refine ⟨mul_pos hH hi, mul_lt_mul_of_pos_right h3 hi,
    mul_le_mul_of_nonneg_right hKb hi.le, ?_⟩
  exact mul_lt_mul_of_pos_right (half_lt_self hH) hi

/-- 归一化 Q0=H/r² 的平方根，显式保留 H、r 的正性。 -/
theorem sqrt_seed_scale_CXSP {H r : ℝ} (hH : 0 < H) (hr : 0 < r) :
    Real.sqrt (H * (r ^ 2)⁻¹) = Real.sqrt H / r := by
  rw [Real.sqrt_mul hH.le, Real.sqrt_inv, Real.sqrt_sq hr.le, div_eq_mul_inv]

/-- D=2A√H 恰对应物理半径 2Ar，不依赖测试点。 -/
theorem seed_distance_normalization_CXSP (A : ℝ) {H r : ℝ}
    (hH : 0 < H) (hr : 0 < r) :
    (2 * A * Real.sqrt H) / Real.sqrt (H * (r ^ 2)⁻¹) = 2 * (A * r) := by
  rw [sqrt_seed_scale_CXSP hH hr]
  field_simp [(Real.sqrt_pos.mpr hH).ne', hr.ne']

/-- 同一最短尾段长度 ℓ<Ar 严格小于 D/√Q0。 -/
theorem seed_tail_length_lt_normalized_CXSP {A H r ℓ : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hr : 0 < r) (hℓ : ℓ < A * r) :
    ℓ < (2 * A * Real.sqrt H) / Real.sqrt (H * (r ^ 2)⁻¹) := by
  rw [seed_distance_normalization_CXSP A hH hr]
  have hAr : 0 < A * r := mul_pos hA hr
  linarith

/-- C* 同时支付 Claim 2 的 endpoint trigger 与 10C2 中间点门槛。 -/
theorem claim2_output_constants_CXSP (C C2 : ℝ) :
    0 < max 1 (max C (10 * max C2 1 + 1)) ∧
      C ≤ max 1 (max C (10 * max C2 1 + 1)) ∧
      10 * C2 < max 1 (max C (10 * max C2 1 + 1)) := by
  have h1 : (1 : ℝ) ≤ max 1 (max C (10 * max C2 1 + 1)) := le_max_left _ _
  have hC : C ≤ max 1 (max C (10 * max C2 1 + 1)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC2 : C2 ≤ max C2 1 := le_max_left _ _
  have h10 : 10 * max C2 1 + 1 ≤ max 1 (max C (10 * max C2 1 + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨by linarith, hC, by linarith⟩

/-- 乘回物理尺度：Claim 2 的倍数 C* 与 seed H 合成 K2=H*C*。 -/
theorem scalar_le_seed_product_CXSP {R H C r : ℝ}
    (hR : R ≤ C * (H * (r ^ 2)⁻¹)) :
    R ≤ (H * C) * (r ^ 2)⁻¹ := by
  calc
    R ≤ C * (H * (r ^ 2)⁻¹) := hR
    _ = (H * C) * (r ^ 2)⁻¹ := by ring

end GC.LongTime.Ch11
