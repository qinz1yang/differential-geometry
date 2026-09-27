import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

section

open scoped BigOperators

namespace DifferentialGeometry.Analysis

private theorem exists_sub_lt_of_mul_lt
    (e : ℕ → ℝ) {B η : ℝ} {N : ℕ}
    (hN : 0 ≤ e N) (hzero : e 0 ≤ B) (hB : B < (N : ℝ) * η) :
    ∃ j < N, e j - e (j + 1) < η := by
  have hsum : (∑ j ∈ Finset.range N, (e j - e (j + 1))) <
      ∑ _j ∈ Finset.range N, η := by
    rw [Finset.sum_range_sub', Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact (sub_le_self _ hN).trans_lt (hzero.trans_lt hB)
  obtain ⟨j, hj, hdrop⟩ := Finset.exists_lt_of_sum_lt hsum
  exact ⟨j, Finset.mem_range.mp hj, hdrop⟩

theorem exists_uniform_index_energy_le_of_small_drop
    {ε C B η : ℝ} (hε : 0 < ε) (hC : 0 < C) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∀ e : ℕ → ℝ, ∀ δ : ℝ,
      Antitone e → (∀ k, 0 ≤ e k) → e 0 ≤ B →
      (∀ j, e j - e (j + 1) < ε → e (j + 1) ≤ C * (e j - e (j + 1)) + δ) →
      e N ≤ η + δ := by
  let t : ℝ := min ε (η / C)
  have ht : 0 < t := lt_min hε (div_pos hη hC)
  obtain ⟨N, hN⟩ := exists_nat_gt (B / t)
  have hNpos : 0 < N := by
    have hNreal : (0 : ℝ) < N := (div_nonneg hB ht.le).trans_lt hN
    exact Nat.cast_pos.mp hNreal
  have hBmul : B < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
  refine ⟨N, hNpos, ?_⟩
  intro e δ he hnonneg hzero hdrop
  obtain ⟨j, hj, hjdrop⟩ := exists_sub_lt_of_mul_lt e (hnonneg N) hzero hBmul
  have hsmall : e j - e (j + 1) < ε := hjdrop.trans_le (min_le_left _ _)
  have heta : C * (e j - e (j + 1)) < η := by
    have h := (lt_div_iff₀ hC).mp (hjdrop.trans_le (min_le_right _ _))
    simpa only [mul_comm] using h
  exact (he (Nat.succ_le_iff.mpr hj)).trans
    ((hdrop j hsmall).trans (add_le_add heta.le le_rfl))

end DifferentialGeometry.Analysis

end
