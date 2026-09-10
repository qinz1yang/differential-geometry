import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

namespace DifferentialGeometry.Geometry.Affine

theorem exists_Icc_eq_preimage_affine (s c a b : ℝ) (hs : s ≠ 0) :
    ∃ l r : ℝ, (fun z ↦ s * z + c) ⁻¹' Icc a b = Icc l r ∧
      r - l = (b - a) / |s| := by
  have hpre : (fun z ↦ s * z + c) ⁻¹' Icc a b =
      (fun z ↦ s * z) ⁻¹' Icc (a - c) (b - c) := by
    ext z
    change (a ≤ s * z + c ∧ s * z + c ≤ b) ↔ (a - c ≤ s * z ∧ s * z ≤ b - c)
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  rcases lt_or_gt_of_ne hs with hs | hs
  · refine ⟨(b - c) / s, (a - c) / s, ?_, ?_⟩
    · rw [hpre, preimage_const_mul_Icc_of_neg _ _ hs]
    · rw [abs_of_neg hs]
      ring
  · refine ⟨(a - c) / s, (b - c) / s, ?_, ?_⟩
    · rw [hpre, preimage_const_mul_Icc₀ _ _ hs]
    · rw [abs_of_pos hs]
      ring

theorem exists_Icc_of_comparable_scales
    (α β a b B σ c : ℝ) (hβ : 0 < β)
    (hscale : β ≤ 2 * α) (hwidth : 1 ≤ b - a) (herror : B ≤ α / 4)
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ l r : ℝ, (fun z ↦ σ * (β * z) + c) ⁻¹' Icc (α * a + B) (α * b - B) = Icc l r ∧
      1 / 4 ≤ r - l := by
  have hα : 0 < α := by linarith only [hβ, hscale]
  have hs : σ * β ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp [hβ.ne']
  obtain ⟨l, r, heq, hlen⟩ := exists_Icc_eq_preimage_affine (σ * β) c
    (α * a + B) (α * b - B) hs
  have habs : |σ * β| = β := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos hβ]
  refine ⟨l, r, ?_, ?_⟩
  · simpa only [mul_assoc] using heq
  · rw [hlen, habs]
    apply (le_div_iff₀ hβ).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hwidth hα.le, hscale, herror]

end DifferentialGeometry.Geometry.Affine
