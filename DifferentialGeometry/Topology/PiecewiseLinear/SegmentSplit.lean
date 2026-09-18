import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem segment_union_segment_of_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E]
    {z w q : E} (hq : q ∈ segment ℝ z w) :
    segment ℝ q z ∪ segment ℝ q w = segment ℝ z w := by
  refine Subset.antisymm (union_subset ?_ ?_) ?_
  · exact (convex_segment z w).segment_subset hq (left_mem_segment ℝ z w)
  · exact (convex_segment z w).segment_subset hq (right_mem_segment ℝ z w)
  · obtain ⟨c, d, hc, hd, hcd, hqe⟩ := hq
    have hc' : c = 1 - d := by linarith
    subst hc'
    rintro x ⟨a, b, ha, hb, hab, rfl⟩
    have ha' : a = 1 - b := by linarith
    subst ha'
    rcases le_total b d with h | h
    · refine Or.inl ?_
      rcases eq_or_lt_of_le hd with hd0 | hd0
      · have hb0 : b = 0 := by linarith
        rw [hb0]
        simpa using right_mem_segment ℝ q z
      · refine ⟨b / d, 1 - b / d, div_nonneg hb hd, ?_, by ring, ?_⟩
        · rw [sub_nonneg, div_le_one hd0]
          exact h
        · rw [← hqe]
          have hd' : d ≠ 0 := ne_of_gt hd0
          match_scalars <;> (field_simp; try ring)
    · refine Or.inr ?_
      rcases eq_or_lt_of_le hc with hc0 | hc0
      · have hb1 : b = 1 := by linarith
        rw [hb1]
        simpa using right_mem_segment ℝ q w
      · refine ⟨(1 - b) / (1 - d), 1 - (1 - b) / (1 - d), div_nonneg ha hc, ?_, by ring, ?_⟩
        · rw [sub_nonneg, div_le_one hc0]
          linarith
        · rw [← hqe]
          have hc' : (1 : ℝ) - d ≠ 0 := ne_of_gt hc0
          match_scalars <;> (field_simp; try ring)

end DifferentialGeometry.Topology.PiecewiseLinear
