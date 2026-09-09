import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

open Filter Set
open scoped Topology

namespace Real
theorem tendsto_rpow_mul_exp_neg_div_nhdsGT_zero (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ a * exp (-c / t)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) c hc).comp
    tendsto_inv_nhdsGT_zero
  apply h.congr
  intro t
  simp only [Function.comp_apply, ← rpow_neg_eq_inv_rpow, neg_neg, div_eq_mul_inv]

theorem exists_rpow_mul_exp_neg_div_bound (a T : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc 0 T, t ^ a * exp (-c / t) ≤ C := by
  have hlim := tendsto_rpow_mul_exp_neg_div_nhdsGT_zero a hc
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  have hcont : ContinuousOn (fun t : ℝ => t ^ a * exp (-c / t)) (Icc δ T) := by
    intro t ht
    have ht0 : t ≠ 0 := (hδ.trans_le ht.1).ne'
    exact ((continuousAt_id.rpow_const (Or.inl ht0)).mul
      (continuous_exp.continuousAt.comp (continuousAt_const.div continuousAt_id ht0))).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  by_cases htδ : t < δ
  · exact (hsmall ⟨ht.1, htδ⟩).le.trans (le_max_right _ _)
  · exact (hC (mem_image_of_mem _ ⟨le_of_not_gt htδ, ht.2⟩)).trans (le_max_left _ _)

theorem exists_rpow_mul_exp_neg_div_le_rpow (a b T : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc 0 T, ∀ r : ℝ, c ≤ r →
      t ^ a * exp (-r / t) ≤ C * t ^ b := by
  obtain ⟨C, hC, hbound⟩ := exists_rpow_mul_exp_neg_div_bound (a - b) T hc
  refine ⟨C, hC, ?_⟩
  intro t ht r hr
  have he : exp (-r / t) ≤ exp (-c / t) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hr) ht.1.le)
  calc
    t ^ a * exp (-r / t) ≤ t ^ a * exp (-c / t) :=
      mul_le_mul_of_nonneg_left he (rpow_nonneg ht.1.le _)
    _ = (t ^ (a - b) * exp (-c / t)) * t ^ b := by
      rw [mul_right_comm, ← rpow_add ht.1]
      rw [sub_add_cancel]
    _ ≤ C * t ^ b := mul_le_mul_of_nonneg_right (hbound t ht) (rpow_nonneg ht.1.le _)

end Real
