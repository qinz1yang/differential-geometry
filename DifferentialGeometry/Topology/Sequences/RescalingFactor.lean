import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Cofinite

set_option autoImplicit false

open Filter
open scoped Topology

namespace DifferentialGeometry

theorem exists_rescaling_factor_normalization {R Rl s τ : ℕ → ℝ} (hpos : ∀ n, 0 < Rl n)
    (hRl : Tendsto Rl atTop atTop) (hclose : ∀ n, |R n - Rl n| ≤ Rl n / 2)
    (hτs : ∀ n, τ n < s n) (hgap : ∀ n, (s n - τ n) * Rl n ≤ 1 / ((n : ℝ) + 1)) :
    (∀ n, 0 < R n) ∧ Tendsto R atTop atTop ∧ (∀ c : ℝ, ∃ C : ℝ, ∀ n, c ≤ C * R n) ∧
      Tendsto (fun n => R n * (τ n - s n)) atTop (𝓝 0) := by
  have hlow (n : ℕ) : Rl n / 2 ≤ R n := by
    have h := (abs_le.mp (hclose n)).1
    linarith
  have hup (n : ℕ) : R n ≤ 3 * Rl n / 2 := by
    have h := (abs_le.mp (hclose n)).2
    linarith
  have hRpos (n : ℕ) : 0 < R n := (half_pos (hpos n)).trans_le (hlow n)
  refine ⟨hRpos, tendsto_atTop_mono hlow (hRl.atTop_div_const two_pos), fun c => ?_, ?_⟩
  · have hcof : Tendsto R cofinite atTop := by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_atTop_mono hlow (hRl.atTop_div_const two_pos)
    obtain ⟨m, hm⟩ := hcof.exists_forall_le
    refine ⟨max c 0 / R m, fun n => ?_⟩
    have h1 : max c 0 / R m * R m ≤ max c 0 / R m * R n :=
      mul_le_mul_of_nonneg_left (hm n) (div_nonneg (le_max_right _ _) (hRpos m).le)
    rw [div_mul_cancel₀ _ (hRpos m).ne'] at h1
    exact (le_max_left _ _).trans h1
  · have hlim : Tendsto (fun n : ℕ => 3 / 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3 / 2 : ℝ)
    have hneg : Tendsto (fun n : ℕ => -(3 / 2 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      simpa using hlim.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hneg tendsto_const_nhds (fun n => ?_)
      (fun n => ?_)
    · have hg : 0 < s n - τ n := sub_pos.mpr (hτs n)
      have h1 : R n * (s n - τ n) ≤ 3 * Rl n / 2 * (s n - τ n) :=
        mul_le_mul_of_nonneg_right (hup n) hg.le
      have h2 : 3 / 2 * ((s n - τ n) * Rl n) ≤ 3 / 2 * (1 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hgap n) (by norm_num)
      change -(3 / 2 * (1 / ((n : ℝ) + 1))) ≤ R n * (τ n - s n)
      nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos (hRpos n).le (sub_nonpos.mpr (hτs n).le)

end DifferentialGeometry
