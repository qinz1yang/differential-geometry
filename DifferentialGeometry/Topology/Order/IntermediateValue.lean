import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

open Set

theorem ContinuousOn.exists_eq_and_forall_gt
    {α β : Type*} [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
    {f : α → β} {a b : α} {c : β}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (ha : f a ≤ c) (hb : c < f b) :
    ∃ s ∈ Ico a b, f s = c ∧ ∀ t ∈ Ioc s b, c < f t := by
  have hne : (Icc a b ∩ f ⁻¹' {c}).Nonempty := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab hf ⟨ha, hb.le⟩
    exact ⟨s, hs, hfs⟩
  have hcompact : IsCompact (Icc a b ∩ f ⁻¹' {c}) :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨s, hs, hmax⟩ := hcompact.exists_isGreatest hne
  have hfs : f s = c := hs.2
  have hsb : s < b := lt_of_le_of_ne hs.1.2 (by intro h; subst s; exact hb.ne' hfs)
  refine ⟨s, ⟨hs.1.1, hsb⟩, hfs, fun t ht => ?_⟩
  by_contra h
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc ht.2
    (hf.mono (Icc_subset_Icc (hs.1.1.trans ht.1.le) le_rfl))
    ⟨le_of_not_gt h, hb.le⟩
  exact (not_lt_of_ge (hmax ⟨⟨hs.1.1.trans (ht.1.le.trans hu.1), hu.2⟩, hfu⟩))
    (ht.1.trans_le hu.1)
