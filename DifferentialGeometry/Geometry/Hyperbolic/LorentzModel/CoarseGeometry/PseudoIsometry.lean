/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Action

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.PseudoIsometry

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction

variable {n : ℕ}

structure IsPseudoIsometry (K C : ℝ) (Φ : HUpper n → HUpper n) : Prop where
  hK : 1 ≤ K
  hC : 0 ≤ C
  upper : ∀ x y, dist (Φ x) (Φ y) ≤ K * dist x y + C
  lower : ∀ x y, K⁻¹ * dist x y - C ≤ dist (Φ x) (Φ y)

theorem isPseudoIsometry_id : IsPseudoIsometry (1 : ℝ) (0 : ℝ) (id : HUpper n → HUpper n) where
  hK := le_refl 1
  hC := le_refl 0
  upper x y := by
    change dist x y ≤ 1 * dist x y + 0
    rw [one_mul, add_zero]
  lower x y := by
    change 1⁻¹ * dist x y - 0 ≤ dist x y
    rw [inv_one, one_mul, sub_zero]

theorem isPseudoIsometry_of_isometry {Φ : HUpper n → HUpper n}
    (h : ∀ x y, dist (Φ x) (Φ y) = dist x y) : IsPseudoIsometry (1 : ℝ) (0 : ℝ) Φ where
  hK := le_refl 1
  hC := le_refl 0
  upper x y := by rw [h, one_mul, add_zero]
  lower x y := by rw [h, inv_one, one_mul, sub_zero]

theorem isPseudoIsometry_po_smul (hn : 1 ≤ n) (g : PO n 1) :
    IsPseudoIsometry (1 : ℝ) (0 : ℝ) (fun x => (poMulAction hn).smul g x) :=
  isPseudoIsometry_of_isometry fun x y => po_dist_smul hn g x y

theorem IsPseudoIsometry.comp {K₁ C₁ K₂ C₂ : ℝ} {Φ₁ Φ₂ : HUpper n → HUpper n}
    (h₁ : IsPseudoIsometry K₁ C₁ Φ₁) (h₂ : IsPseudoIsometry K₂ C₂ Φ₂) :
    IsPseudoIsometry (K₁ * K₂) (K₁ * C₂ + C₁) (Φ₁ ∘ Φ₂) where
  hK := one_le_mul_of_one_le_of_one_le h₁.hK h₂.hK
  hC := add_nonneg (mul_nonneg (zero_le_one.trans h₁.hK) h₂.hC) h₁.hC
  upper x y := by
    calc dist ((Φ₁ ∘ Φ₂) x) ((Φ₁ ∘ Φ₂) y) = dist (Φ₁ (Φ₂ x)) (Φ₁ (Φ₂ y)) := rfl
      _ ≤ K₁ * dist (Φ₂ x) (Φ₂ y) + C₁ := h₁.upper _ _
      _ ≤ K₁ * (K₂ * dist x y + C₂) + C₁ :=
        add_le_add_left (mul_le_mul_of_nonneg_left (h₂.upper x y)
          (zero_le_one.trans h₁.hK)) C₁
      _ = K₁ * K₂ * dist x y + (K₁ * C₂ + C₁) := by ring
  lower x y := by
    have hK₁0 : (0 : ℝ) < K₁ := zero_lt_one.trans_le h₁.hK
    have hinv : K₁⁻¹ ≤ K₁ := (inv_le_one_of_one_le₀ h₁.hK).trans h₁.hK
    calc (K₁ * K₂)⁻¹ * dist x y - (K₁ * C₂ + C₁)
        = K₁⁻¹ * K₂⁻¹ * dist x y - (K₁ * C₂ + C₁) := by rw [mul_inv]
      _ ≤ K₁⁻¹ * K₂⁻¹ * dist x y - (K₁⁻¹ * C₂ + C₁) :=
        sub_le_sub_left
          (add_le_add_left
            (mul_le_mul hinv (le_refl C₂) h₂.hC hK₁0.le) C₁) _
      _ = K₁⁻¹ * (K₂⁻¹ * dist x y - C₂) - C₁ := by ring
      _ ≤ K₁⁻¹ * dist (Φ₂ x) (Φ₂ y) - C₁ :=
        sub_le_sub_right
          (mul_le_mul_of_nonneg_left (h₂.lower x y) (inv_nonneg.mpr hK₁0.le)) C₁
      _ ≤ dist (Φ₁ (Φ₂ x)) (Φ₁ (Φ₂ y)) := h₁.lower _ _

def IsFEquivariant {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ) (hn : 1 ≤ n)
    (Φ : HUpper n → HUpper n) : Prop :=
  ∀ (γ : Γ) (x : HUpper n), Φ ((poMulAction hn).smul (γ : PO n 1) x)
    = (poMulAction hn).smul (f γ : PO n 1) (Φ x)

end DifferentialGeometry.PseudoIsometry
