import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GC.Surgery
set_option autoImplicit false

theorem separate_horizon_profiles :
    ∀ B : ℝ, 1 ≤ B → ∃ δ : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ B →
      0 < δ t ∧ δ t ≤ 1 / B := by
  intro B hB
  exact ⟨fun _ => 1 / B, fun _ _ _ => ⟨one_div_pos.mpr (by linarith), le_rfl⟩⟩

theorem no_single_profile :
    ¬ ∃ δ : ℝ → ℝ, ∀ B : ℝ, 1 ≤ B → ∀ t : ℝ, 0 ≤ t → t ≤ B →
      0 < δ t ∧ δ t ≤ 1 / B := by
  rintro ⟨δ, hδ⟩
  have hd := (hδ 1 le_rfl 1 zero_le_one le_rfl).1
  let B : ℝ := max 1 (2 / δ 1)
  have hB : 1 ≤ B := le_max_left _ _
  have hpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hup := (hδ B hB 1 zero_le_one hB).2
  have hprod : B * δ 1 ≤ 1 := by
    have := (le_div_iff₀ hpos).mp hup
    simpa only [mul_comm] using this
  have hlo : 2 ≤ B * δ 1 := (div_le_iff₀ hd).mp (le_max_right 1 (2 / δ 1))
  linarith

theorem finite_horizon_choice_does_not_supply_one_profile :
    (∀ B : ℝ, 1 ≤ B → ∃ δ : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ B →
      0 < δ t ∧ δ t ≤ 1 / B) ∧
    ¬ (∃ δ : ℝ → ℝ, ∀ B : ℝ, 1 ≤ B → ∀ t : ℝ, 0 ≤ t → t ≤ B →
      0 < δ t ∧ δ t ≤ 1 / B) :=
  ⟨separate_horizon_profiles, no_single_profile⟩

end GC.Surgery
