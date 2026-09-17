import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

open Set Metric

private theorem exists_pos_smul_sub_of_mem_segment_ne_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] {a b x : E}
    (hx : x ∈ segment ℝ a b) (hxa : x ≠ a) :
    ∃ t : ℝ, 0 < t ∧ x - a = t • (b - a) := by
  obtain ⟨u, v, _, hv, huv, h⟩ := hx
  have hu : u = 1 - v := by linarith only [huv]
  have hsub : x - a = v • (b - a) := by
    rw [← h, hu]
    module
  have hvne : v ≠ 0 := by
    intro he
    rw [he, zero_smul] at hsub
    exact hxa (sub_eq_zero.mp hsub)
  exact ⟨v, lt_of_le_of_ne hv (Ne.symm hvne), hsub⟩

theorem sameRay_or_of_local_segment_subset
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {a b c d : E} {U : Set E} (hU : IsOpen U) (haU : a ∈ U)
    (hlocal : ∀ x ∈ U, x ∈ segment ℝ a b →
      x ∈ segment ℝ a c ∪ segment ℝ a d) :
    SameRay ℝ (b - a) (c - a) ∨ SameRay ℝ (b - a) (d - a) := by
  by_cases hba : b = a
  · exact Or.inl (by rw [hba, sub_self]; exact SameRay.zero_left _)
  have hcont : Continuous (fun t : ℝ => a + t • (b - a)) := by fun_prop
  have hzero : (0 : ℝ) ∈ (fun t : ℝ => a + t • (b - a)) ⁻¹' U := by
    simpa only [mem_preimage, zero_smul, add_zero] using haU
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hcont) 0 hzero
  let t : ℝ := min δ 1 / 2
  have ht : 0 < t := half_pos (lt_min hδ zero_lt_one)
  have htδ : t < δ := (half_lt_self (lt_min hδ zero_lt_one)).trans_le (min_le_left _ _)
  have ht1 : t < 1 := (half_lt_self (lt_min hδ zero_lt_one)).trans_le (min_le_right _ _)
  let x : E := a + t • (b - a)
  have hxU : x ∈ U := hδU (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact htδ)
  have hxab : x ∈ segment ℝ a b := by
    refine ⟨1 - t, t, sub_nonneg.mpr ht1.le, ht.le, by ring, ?_⟩
    dsimp [x]
    module
  have hxsub : x - a = t • (b - a) := add_sub_cancel_left _ _
  have hxa : x ≠ a := by
    intro he
    have hz : t • (b - a) = 0 := by rw [← hxsub, he, sub_self]
    exact (smul_ne_zero ht.ne' (sub_ne_zero.mpr hba)) hz
  rcases hlocal x hxU hxab with hxc | hxd
  · obtain ⟨v, hv, hxv⟩ := exists_pos_smul_sub_of_mem_segment_ne_left hxc hxa
    exact Or.inl (Or.inr (Or.inr ⟨t, v, ht, hv, hxsub.symm.trans hxv⟩))
  · obtain ⟨v, hv, hxv⟩ := exists_pos_smul_sub_of_mem_segment_ne_left hxd hxa
    exact Or.inr (Or.inr (Or.inr ⟨t, v, ht, hv, hxsub.symm.trans hxv⟩))
