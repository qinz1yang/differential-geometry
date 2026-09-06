import Mathlib.Topology.Order.Basic

open Set Filter
open scoped Topology

theorem Set.OrdConnected.exists_Icc_subset_mem_nhdsWithin
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {J : Set α} {t₀ t : α} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    ∃ a b, t₀ ∈ Icc a b ∧ t ∈ Icc a b ∧ Icc a b ⊆ J ∧ Icc a b ∈ 𝓝[J] t := by
  have hlower : ∃ a ∈ J, a ≤ t₀ ∧ a ≤ t ∧ Ici a ∈ 𝓝[J] t := by
    by_cases h : ∃ l ∈ J, l < t
    · obtain ⟨l, hl, hlt⟩ := h
      refine ⟨min t₀ l, ?_, min_le_left _ _, (min_le_right _ _).trans hlt.le, ?_⟩
      · rcases le_total t₀ l with hle | hle
        · simpa only [min_eq_left hle] using ht₀
        · simpa only [min_eq_right hle] using hl
      · exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ((min_le_right _ _).trans_lt hlt))
    · refine ⟨min t₀ t, ?_, min_le_left _ _, min_le_right _ _, ?_⟩
      · rcases le_total t₀ t with hle | hle
        · simpa only [min_eq_left hle] using ht₀
        · simpa only [min_eq_right hle] using ht
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact (min_le_right _ _).trans (not_lt.mp (fun hrt => h ⟨r, hr, hrt⟩))
  have hupper : ∃ b ∈ J, t₀ ≤ b ∧ t ≤ b ∧ Iic b ∈ 𝓝[J] t := by
    by_cases h : ∃ r ∈ J, t < r
    · obtain ⟨r, hr, htr⟩ := h
      refine ⟨max t₀ r, ?_, le_max_left _ _, htr.le.trans (le_max_right _ _), ?_⟩
      · rcases le_total t₀ r with hle | hle
        · simpa only [max_eq_right hle] using hr
        · simpa only [max_eq_left hle] using ht₀
      · exact mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (htr.trans_le (le_max_right _ _)))
    · refine ⟨max t₀ t, ?_, le_max_left _ _, le_max_right _ _, ?_⟩
      · rcases le_total t₀ t with hle | hle
        · simpa only [max_eq_right hle] using ht
        · simpa only [max_eq_left hle] using ht₀
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact (not_lt.mp (fun htr => h ⟨r, hr, htr⟩)).trans (le_max_right _ _)
  obtain ⟨a, ha, ha₀, hat, hna⟩ := hlower
  obtain ⟨b, hb, hb₀, htb, hnb⟩ := hupper
  exact ⟨a, b, ⟨ha₀, hb₀⟩, ⟨hat, htb⟩, hJ.out ha hb, Filter.inter_mem hna hnb⟩
