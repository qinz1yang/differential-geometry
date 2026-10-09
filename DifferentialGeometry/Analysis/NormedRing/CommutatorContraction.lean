/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Set Filter
open scoped Topology commutatorElement

namespace DifferentialGeometry.Zassenhaus

section NormedRing

variable {G R : Type*} [Group G] [NormedRing R]

def size (ρ : G →* Rˣ) (a : G) : ℝ :=
  max ‖(ρ a).val - 1‖ ‖(ρ a⁻¹).val - 1‖

theorem size_nonneg (ρ : G →* Rˣ) (a : G) : 0 ≤ size ρ a :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem norm_sub_one_le_size (ρ : G →* Rˣ) (a : G) :
    ‖(ρ a).val - 1‖ ≤ size ρ a := le_max_left _ _

theorem norm_inv_sub_one_le_size (ρ : G →* Rˣ) (a : G) :
    ‖(ρ a⁻¹).val - 1‖ ≤ size ρ a := le_max_right _ _

@[simp] theorem size_one (ρ : G →* Rˣ) : size ρ 1 = 0 := by
  simp [size]

@[simp] theorem size_inv (ρ : G →* Rˣ) (a : G) : size ρ a⁻¹ = size ρ a := by
  simp only [size, inv_inv, max_comm]

variable [NormOneClass R]

theorem norm_inv_le_two (ρ : G →* Rˣ) {a : G} (ha : size ρ a ≤ 1 / 16) :
    ‖(ρ a⁻¹).val‖ ≤ 2 := by
  have h := norm_add_le ((ρ a⁻¹).val - 1) (1 : R)
  rw [sub_add_cancel, norm_one] at h
  linarith [norm_inv_sub_one_le_size ρ a]

theorem norm_commutator_le (ρ : G →* Rˣ) {a b : G}
    (ha : size ρ a ≤ 1 / 16) (hb : size ρ b ≤ 1 / 16) :
    ‖(ρ ⁅a, b⁆).val - 1‖ ≤ 8 * size ρ a * size ρ b := by
  have ha0 := size_nonneg ρ a
  have hb0 := size_nonneg ρ b
  calc
    ‖(ρ ⁅a, b⁆).val - 1‖
        ≤ 2 * ‖(ρ a⁻¹).val‖ * ‖(ρ b⁻¹).val‖ * ‖(ρ a).val - 1‖ * ‖(ρ b).val - 1‖ := by
      simpa only [commutatorElement_def, map_mul, map_inv] using
        norm_commutator_units_sub_one_le (ρ a) (ρ b)
    _ ≤ 2 * 2 * 2 * size ρ a * size ρ b := by
      gcongr
      · exact norm_inv_le_two ρ ha
      · exact norm_inv_le_two ρ hb
      · exact norm_sub_one_le_size ρ a
      · exact norm_sub_one_le_size ρ b
    _ = 8 * size ρ a * size ρ b := by ring

theorem size_commutator_le (ρ : G →* Rˣ) {a b : G}
    (ha : size ρ a ≤ 1 / 16) (hb : size ρ b ≤ 1 / 16) :
    size ρ ⁅a, b⁆ ≤ 8 * size ρ a * size ρ b := by
  apply max_le (norm_commutator_le ρ ha hb)
  rw [commutatorElement_inv]
  calc
    ‖(ρ ⁅b, a⁆).val - 1‖ ≤ 8 * size ρ b * size ρ a := norm_commutator_le ρ hb ha
    _ = 8 * size ρ a * size ρ b := by ring

theorem size_commutator_contract (ρ : G →* Rˣ) {a b : G}
    (ha : size ρ a ≤ 1 / 16) (hb : size ρ b ≤ 1 / 16) :
    size ρ ⁅a, b⁆ ≤ (1 / 2) * size ρ a := by
  calc
    size ρ ⁅a, b⁆ ≤ 8 * size ρ a * size ρ b := size_commutator_le ρ ha hb
    _ ≤ 8 * size ρ a * (1 / 16) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) (size_nonneg ρ a))
    _ = (1 / 2) * size ρ a := by ring

end NormedRing

end DifferentialGeometry.Zassenhaus
