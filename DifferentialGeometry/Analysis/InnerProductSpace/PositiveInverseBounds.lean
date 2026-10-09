import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem isUnit_of_inner_lower_bound (A : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hA : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) : IsUnit A := by
  apply A.isUnit_of_forall_le_norm_inner_map (c := ⟨a, ha.le⟩) ha
  intro x
  change ‖x‖ ^ 2 * a ≤ |⟪A x, x⟫_ℝ|
  rw [mul_comm]
  exact (hA x).trans (le_abs_self _)

private theorem apply_inverse_of_inner_lower_bound (A : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hA : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) (x : E) :
    A ((Ring.inverse A) x) = x := by
  have h := congrArg (fun B : E →L[ℝ] E => B x)
    (Ring.mul_inverse_cancel A (isUnit_of_inner_lower_bound A ha hA))
  exact h

theorem norm_inverse_apply_le_of_inner_lower_bound (A : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hA : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) (x : E) :
    ‖(Ring.inverse A) x‖ ≤ ‖x‖ / a := by
  have hl := hA ((Ring.inverse A) x)
  rw [apply_inverse_of_inner_lower_bound A ha hA] at hl
  have hu := real_inner_le_norm x ((Ring.inverse A) x)
  apply (le_div_iff₀ ha).mpr
  by_cases hz : ‖(Ring.inverse A) x‖ = 0
  · simp [hz]
  · have hp : 0 < ‖(Ring.inverse A) x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

theorem inner_inverse_apply_lower_bound (A : E →L[ℝ] E) (hpos : A.IsPositive)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hupper : ∀ x : E, ⟪A x, x⟫_ℝ ≤ b * ‖x‖ ^ 2) (x y : E) :
    ‖x‖ ^ 2 / b - ‖y - x‖ * ‖x‖ / a ≤ ⟪x, (Ring.inverse A) y⟫_ℝ := by
  let z := (Ring.inverse A) x
  have haz : A z = x := apply_inverse_of_inner_lower_bound A ha hlower x
  have hz : ‖x‖ ^ 2 / b ≤ ⟪x, z⟫_ℝ := by
    have hp := hpos.inner_nonneg_left (z - b⁻¹ • x)
    have hsym := hpos.inner_left_eq_inner_right x z
    rw [haz, real_inner_self_eq_norm_sq] at hsym
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, haz,
      real_inner_self_eq_norm_sq] at hp
    have hu := hupper x
    have hscale := mul_le_mul_of_nonneg_left hu (sq_nonneg b⁻¹)
    rw [← hsym] at hp
    have hid : b⁻¹ * b = 1 := inv_mul_cancel₀ hb.ne'
    apply (div_le_iff₀ hb).mpr
    field_simp at hp
    nlinarith
  have he : ⟪x, (Ring.inverse A) y⟫_ℝ =
      ⟪x, z⟫_ℝ + ⟪x, (Ring.inverse A) (y - x)⟫_ℝ := by
    rw [map_sub, inner_sub_right]
    dsimp [z]
    ring
  rw [he]
  have he' := abs_real_inner_le_norm x ((Ring.inverse A) (y - x))
  have hn := norm_inverse_apply_le_of_inner_lower_bound A ha hlower (y - x)
  have hbound := mul_le_mul_of_nonneg_left hn (norm_nonneg x)
  have hneg := (abs_le.mp he').1
  rw [← mul_div_assoc] at hbound
  have hcomm : ‖x‖ * ‖y - x‖ / a = ‖y - x‖ * ‖x‖ / a := by ring
  rw [hcomm] at hbound
  linarith

theorem dual_apply_inverse_lower_bound (A : E →L[ℝ] E) (hpos : A.IsPositive)
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlower : ∀ x : E, (1 - δ) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hupper : ∀ x : E, ⟪A x, x⟫_ℝ ≤ (1 + δ) * ‖x‖ ^ 2)
    (β ξ : StrongDual ℝ E) (herror : ‖ξ - β‖ ≤ σ) :
    ‖β‖ ^ 2 / (1 + δ) - σ * ‖β‖ / (1 - δ) ≤
      β ((Ring.inverse A) ((InnerProductSpace.toDual ℝ E).symm ξ)) := by
  have h := inner_inverse_apply_lower_bound A hpos
    (a := 1 - δ) (b := 1 + δ) (by linarith) (by linarith) hlower hupper
    ((InnerProductSpace.toDual ℝ E).symm β) ((InnerProductSpace.toDual ℝ E).symm ξ)
  rw [InnerProductSpace.toDual_symm_apply, ← map_sub] at h
  simp only [LinearIsometryEquiv.norm_map] at h
  have he := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right herror (norm_nonneg β)) (by linarith : 0 ≤ 1 - δ)
  linarith

theorem dual_apply_inverse_pos (A : E →L[ℝ] E) (hpos : A.IsPositive)
    {δ σ m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlower : ∀ x : E, (1 - δ) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hupper : ∀ x : E, ⟪A x, x⟫_ℝ ≤ (1 + δ) * ‖x‖ ^ 2)
    (β ξ : StrongDual ℝ E) (hm : 0 < m) (hβ : m ≤ ‖β‖)
    (herror : ‖ξ - β‖ ≤ σ) (hbudget : σ < (1 - δ) / (1 + δ) * m) :
    0 < β ((Ring.inverse A) ((InnerProductSpace.toDual ℝ E).symm ξ)) := by
  have hminus : 0 < 1 - δ := by linarith
  have hplus : 0 < 1 + δ := by linarith
  have hβpos : 0 < ‖β‖ := hm.trans_le hβ
  rw [div_mul_eq_mul_div] at hbudget
  have hb := (lt_div_iff₀ hplus).mp hbudget
  have hb' : σ * (1 + δ) < (1 - δ) * ‖β‖ :=
    hb.trans_le (mul_le_mul_of_nonneg_left hβ hminus.le)
  have hp : σ * ‖β‖ / (1 - δ) < ‖β‖ ^ 2 / (1 + δ) := by
    apply (div_lt_div_iff₀ hminus hplus).mpr
    nlinarith [mul_pos (sub_pos.mpr hb') hβpos]
  have hl := dual_apply_inverse_lower_bound A hpos hδ hδ1 hlower hupper β ξ herror
  linarith

end ContinuousLinearMap
