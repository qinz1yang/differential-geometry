import Mathlib.Algebra.Group.Commutator
import Mathlib.Analysis.Normed.Ring.Basic

namespace Units

variable {A : Type*} [SeminormedRing A]

theorem norm_mul_inv_le_of_norm_sub_one_lt_one (a : Aˣ) (x : A)
    (ha : ‖(↑a : A) - 1‖ < 1) :
    ‖x * (↑a⁻¹ : A)‖ ≤ ‖x‖ / (1 - ‖(↑a : A) - 1‖) := by
  have h : ‖x * (↑a⁻¹ : A)‖ ≤ ‖x‖ + ‖x * (↑a⁻¹ : A)‖ * ‖(↑a : A) - 1‖ := by
    calc
      ‖x * (↑a⁻¹ : A)‖ = ‖x - (x * (↑a⁻¹ : A)) * ((↑a : A) - 1)‖ := by
        simp [mul_sub, mul_assoc]
      _ ≤ ‖x‖ + ‖(x * (↑a⁻¹ : A)) * ((↑a : A) - 1)‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ‖x * (↑a⁻¹ : A)‖ * ‖(↑a : A) - 1‖ :=
        add_le_add le_rfl (norm_mul_le _ _)
  apply (le_div_iff₀ (sub_pos.mpr ha)).2
  rw [mul_sub, mul_one]
  exact sub_le_iff_le_add.mpr h

theorem norm_inv_le_of_norm_sub_one_lt_one (a : Aˣ) (ha : ‖(↑a : A) - 1‖ < 1) :
    ‖(↑a⁻¹ : A)‖ ≤ ‖(1 : A)‖ / (1 - ‖(↑a : A) - 1‖) := by
  simpa only [one_mul] using norm_mul_inv_le_of_norm_sub_one_lt_one a (1 : A) ha

open scoped commutatorElement in
theorem norm_commutator_sub_one_le_of_norm_sub_one_le_half
    (a b : Aˣ) (ha : ‖(↑a : A) - 1‖ ≤ 1 / 2) (hb : ‖(↑b : A) - 1‖ ≤ 1 / 2) :
    ‖(↑⁅a, b⁆ : A) - 1‖ ≤ 8 * ‖(↑a : A) - 1‖ * ‖(↑b : A) - 1‖ := by
  have hmul (u : Aˣ) (x : A) (hu : ‖(↑u : A) - 1‖ ≤ 1 / 2) :
      ‖x * (↑u⁻¹ : A)‖ ≤ 2 * ‖x‖ := by
    have hu1 : ‖(↑u : A) - 1‖ < 1 := hu.trans_lt (by norm_num)
    refine (norm_mul_inv_le_of_norm_sub_one_lt_one u x hu1).trans ?_
    apply (div_le_iff₀ (sub_pos.mpr hu1)).2
    calc
      ‖x‖ = 2 * ‖x‖ * (1 - (1 / 2 : ℝ)) := by ring
      _ ≤ 2 * ‖x‖ * (1 - ‖(↑u : A) - 1‖) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hu 1)
          (mul_nonneg (by norm_num) (norm_nonneg x))
  have hcomm : ‖(↑a : A) * ↑b - (↑b : A) * ↑a‖ ≤
      2 * ‖(↑a : A) - 1‖ * ‖(↑b : A) - 1‖ := by
    calc
      _ = ‖((↑a : A) - 1) * ((↑b : A) - 1) - ((↑b : A) - 1) * ((↑a : A) - 1)‖ := by
        congr 1
        simp only [sub_one_mul, mul_sub_one]
        abel
      _ ≤ ‖((↑a : A) - 1) * ((↑b : A) - 1)‖ +
          ‖((↑b : A) - 1) * ((↑a : A) - 1)‖ := norm_sub_le _ _
      _ ≤ ‖(↑a : A) - 1‖ * ‖(↑b : A) - 1‖ +
          ‖(↑b : A) - 1‖ * ‖(↑a : A) - 1‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = _ := by ring
  calc
    _ = ‖(((↑a : A) * ↑b - (↑b : A) * ↑a) * (↑a⁻¹ : A)) * (↑b⁻¹ : A)‖ := by
      simp [commutatorElement_def, sub_mul, mul_assoc]
    _ ≤ 2 * ‖((↑a : A) * ↑b - (↑b : A) * ↑a) * (↑a⁻¹ : A)‖ := hmul b _ hb
    _ ≤ 2 * (2 * ‖(↑a : A) * ↑b - (↑b : A) * ↑a‖) :=
      mul_le_mul_of_nonneg_left (hmul a _ ha) (by norm_num)
    _ ≤ 2 * (2 * (2 * ‖(↑a : A) - 1‖ * ‖(↑b : A) - 1‖)) := by gcongr
    _ = _ := by ring

end Units
