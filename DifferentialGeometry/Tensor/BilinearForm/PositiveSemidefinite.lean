import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem IsPosSemidef.abs_apply_le_mul_self_add_inv_mul_self
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hB : B.IsPosSemidef) (x y : V) {η : ℝ} (hη : 0 < η) :
    |B x y| ≤ (η * B x x + η⁻¹ * B y y) / 2 := by
  have hp := hB.nonneg (η • x + y)
  have hm := hB.nonneg (η • x - y)
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
    smul_eq_mul] at hp hm
  rw [show B y x = B x y from hB.eq y x] at hp hm
  apply (mul_le_mul_iff_right₀ hη).mp
  calc
    η * |B x y| ≤ (η ^ 2 * B x x + B y y) / 2 := by
      by_cases hxy : 0 ≤ B x y
      · rw [abs_of_nonneg hxy]
        nlinarith only [hm]
      · rw [abs_of_neg (lt_of_not_ge hxy)]
        nlinarith only [hp]
    _ = η * ((η * B x x + η⁻¹ * B y y) / 2) := by
      field_simp [ne_of_gt hη]

theorem IsPosSemidef.abs_apply_sub_apply_le_energy
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hB : B.IsPosSemidef) (x₁ x₂ y₁ y₂ : V)
    {η : ℝ} (hη : 0 < η) :
    |B x₁ x₂ - B y₁ y₂| ≤
      η * (B x₁ x₁ + B x₂ x₂) +
        (η⁻¹ + 1) * (B (x₁ - y₁) (x₁ - y₁) + B (x₂ - y₂) (x₂ - y₂)) := by
  have h₁ := hB.abs_apply_le_mul_self_add_inv_mul_self x₁ (x₂ - y₂) hη
  have h₂ := hB.abs_apply_le_mul_self_add_inv_mul_self x₂ (x₁ - y₁) hη
  have h₃ := hB.abs_apply_le_mul_self_add_inv_mul_self (x₁ - y₁) (x₂ - y₂)
    (show (0 : ℝ) < 1 by norm_num)
  have hid : B x₁ x₂ - B y₁ y₂ = B x₁ (x₂ - y₂) + B x₂ (x₁ - y₁) -
      B (x₁ - y₁) (x₂ - y₂) := by
    simp only [map_sub, sub_apply]
    rw [show B x₂ x₁ = B x₁ x₂ from hB.eq x₂ x₁,
      show B x₂ y₁ = B y₁ x₂ from hB.eq x₂ y₁]
    ring
  have htriangle : |B x₁ x₂ - B y₁ y₂| ≤
      |B x₁ (x₂ - y₂)| + |B x₂ (x₁ - y₁)| + |B (x₁ - y₁) (x₂ - y₂)| := by
    rw [hid]
    exact (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
  simp only [one_mul, inv_one] at h₃
  have hx₁ := hB.nonneg x₁
  have hx₂ := hB.nonneg x₂
  have hd₁ := hB.nonneg (x₁ - y₁)
  have hd₂ := hB.nonneg (x₂ - y₂)
  have hlarge : 0 ≤ η * (B x₁ x₁ + B x₂ x₂) +
      (η⁻¹ + 1) * (B (x₁ - y₁) (x₁ - y₁) + B (x₂ - y₂) (x₂ - y₂)) := by
    positivity
  linarith

end LinearMap

end
