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

theorem ContinuousOn.exists_first_level_of_compact
    {α β X : Type*} [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
    [TopologicalSpace X] [CompactSpace X]
    {f : α × X → β} {a b : α} {c : β}
    (hf : ContinuousOn f (Icc a b ×ˢ univ)) (hab : a ≤ b)
    (ha : ∀ x : X, f (a, x) < c) (hb : ∃ x : X, c ≤ f (b, x)) :
    ∃ t ∈ Ioc a b, ∃ x : X, f (t, x) = c ∧
      (∀ s ∈ Ico a t, ∀ y : X, f (s, y) < c) ∧
      ∀ y : X, f (t, y) ≤ c := by
  let K : Set (α × X) := {p ∈ Icc a b ×ˢ univ | c ≤ f p}
  have hKclosed : IsClosed K :=
    (isClosed_Icc.prod isClosed_univ).isClosed_le continuousOn_const hf
  have hKcompact : IsCompact K :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set X))).of_isClosed_subset
      hKclosed (fun _ hp => hp.1)
  have hKnonempty : K.Nonempty := by
    obtain ⟨x, hx⟩ := hb
    exact ⟨(b, x), ⟨⟨hab, le_rfl⟩, mem_univ x⟩, hx⟩
  obtain ⟨p, hp, hmin⟩ := hKcompact.exists_isMinOn hKnonempty continuous_fst.continuousOn
  have hbelow : ∀ s ∈ Icc a p.1, ∀ y : X, f (s, y) ≤ c := by
    intro s hs y
    by_contra h
    have hhigh : c < f (s, y) := lt_of_not_ge h
    have hcs : ContinuousOn (fun t => f (t, y)) (Icc a s) :=
      hf.comp (f := fun t : α => (t, y))
        (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨⟨ht.1, ht.2.trans (hs.2.trans hp.1.1.2)⟩, mem_univ y⟩)
    obtain ⟨t, ht, heq⟩ := intermediate_value_Ico hs.1 hcs ⟨(ha y).le, hhigh⟩
    have htK : (t, y) ∈ K :=
      ⟨⟨⟨ht.1, ht.2.le.trans (hs.2.trans hp.1.1.2)⟩, mem_univ y⟩, heq.symm.le⟩
    exact (not_lt_of_ge (hmin htK)) (ht.2.trans_le hs.2)
  have heq : f p = c := le_antisymm (hbelow p.1 ⟨hp.1.1.1, le_rfl⟩ p.2) hp.2
  have hapt : a < p.1 := lt_of_le_of_ne hp.1.1.1 (fun hap =>
    (ha p.2).ne (by simpa only [hap] using heq))
  refine ⟨p.1, ⟨hapt, hp.1.1.2⟩, p.2, heq, ?_, hbelow p.1 ⟨hapt.le, le_rfl⟩⟩
  intro s hs y
  by_contra h
  have hsK : (s, y) ∈ K :=
    ⟨⟨⟨hs.1, hs.2.le.trans hp.1.1.2⟩, mem_univ y⟩, le_of_not_gt h⟩
  exact (not_lt_of_ge (hmin hsK)) hs.2
