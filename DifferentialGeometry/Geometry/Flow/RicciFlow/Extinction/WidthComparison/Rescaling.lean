import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ScalarComparison

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

private theorem mul_mem_Icc {r H t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 (H / r)) :
    r * t ∈ Icc 0 H := by
  refine ⟨mul_nonneg hr.le ht.1, ?_⟩
  simpa only [mul_comm] using (le_div_iff₀ hr).mp ht.2

private theorem mul_mem_Ico {r H t : ℝ} (hr : 0 < r) (ht : t ∈ Ico 0 (H / r)) :
    r * t ∈ Ico 0 H := by
  refine ⟨mul_nonneg hr.le ht.1, ?_⟩
  simpa only [mul_comm] using (lt_div_iff₀ hr).mp ht.2

theorem ScalarComparisonHypotheses.rescale {c H r : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) (hr : 0 < r) :
    ScalarComparisonHypotheses (c / r) (H / r) ((fun t => r * t) ⁻¹' E)
      (fun t => r⁻¹ * W (r * t)) := by
  refine
    { c_pos := div_pos h.c_pos hr
      horizon_pos := div_pos h.horizon_pos hr
      finite_events := ?_
      events_subset := ?_
      nonneg := ?_
      continuous := ?_
      right_continuous := ?_
      incoming_jump := ?_
      dini := ?_ }
  · exact Set.Finite.preimage
      (fun _ _ _ _ hxy => mul_left_cancel₀ hr.ne' hxy) h.finite_events
  · intro t ht
    have htH := h.events_subset ht
    refine ⟨?_, (le_div_iff₀ hr).mpr ?_⟩
    · nlinarith [htH.1]
    · nlinarith [htH.2]
  · intro t ht
    exact mul_nonneg (inv_pos.mpr hr).le (h.nonneg (r * t) (mul_mem_Icc hr ht))
  · intro t ht htE
    exact ((h.continuous (r * t) (mul_mem_Icc hr ht) htE).comp
      (continuous_const.mul continuous_id).continuousWithinAt
      (fun _ hs => mul_mem_Icc hr hs)).const_mul r⁻¹
  · intro t ht
    exact ((h.right_continuous (r * t) (mul_mem_Ico hr ht)).comp
      (continuous_const.mul continuous_id).continuousWithinAt
      (fun _ hs => mul_le_mul_of_nonneg_left hs hr.le)).const_mul r⁻¹
  · intro t ht
    exact incoming_liminf_rescale hr (h.incoming_jump (r * t) ht)
  · intro t ht htE
    have hd := upperRightDiniLE_rescale hr (h.dini (r * t) (mul_mem_Ico hr ht) htE)
    have heq : -2 * Real.pi + 3 * W (r * t) / (4 * (r * t + c)) =
        -2 * Real.pi + 3 * (r⁻¹ * W (r * t)) / (4 * (t + c / r)) := by
      have htc : 0 < t + c / r := add_pos_of_nonneg_of_pos ht.1 (div_pos h.c_pos hr)
      have hs : r * t + c = r * (t + c / r) := by field_simp
      rw [hs]
      field_simp [hr.ne', htc.ne']
    rw [heq] at hd
    exact hd

theorem scalarComparison_initial_bound_rescale {W : ℝ → ℝ} {A r : ℝ}
    (hr : 0 < r) (hA : W 0 ≤ A) : r⁻¹ * W (r * 0) ≤ A / r := by
  simpa only [mul_zero, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hA (inv_pos.mpr hr).le

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
