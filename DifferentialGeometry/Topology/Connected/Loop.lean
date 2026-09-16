import Mathlib.Topology.Order.IntermediateValue

open Set

namespace DifferentialGeometry.Topology

variable {X α : Type*} [TopologicalSpace X] [TopologicalSpace α]
  [ConditionallyCompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α]

theorem isConnected_image_Icc_sdiff_singleton {f : α → X} {a b : α} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b) (hinj : InjOn f (Ico a b)) (p : X) :
    IsConnected (f '' Icc a b \ {p}) := by
  by_cases hp : p ∈ f '' Icc a b
  · obtain ⟨t, ht, htp⟩ := hp
    have hparam : ∃ t ∈ Ico a b, f t = p := by
      by_cases htb : t = b
      · exact ⟨a, ⟨le_rfl, hab⟩, hclose.trans (htb ▸ htp)⟩
      · exact ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩, htp⟩
    obtain ⟨t, ht, rfl⟩ := hparam
    have heq (s : α) (hs : s ∈ Icc a b) : f s = f t ↔ s = t ∨ s = b ∧ t = a := by
      by_cases hsb : s = b
      · subst s
        rw [← hclose]
        constructor
        · intro h
          exact Or.inr ⟨rfl, (hinj ⟨le_rfl, hab⟩ ht h).symm⟩
        · rintro (h | ⟨-, rfl⟩)
          · exact (ht.2.ne (h.symm)).elim
          · rfl
      · constructor
        · exact fun h => Or.inl (hinj ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩ ht h)
        · rintro (rfl | ⟨h, -⟩)
          · rfl
          · exact (hsb h).elim
    by_cases hta : t = a
    · subst t
      have himage : f '' Icc a b \ {f a} = f '' Ioo a b := by
        ext x
        constructor
        · rintro ⟨⟨s, hs, rfl⟩, hsf⟩
          have hne := mt (heq s hs).mpr hsf
          exact ⟨s, ⟨lt_of_le_of_ne hs.1 (fun h => hne (Or.inl h.symm)),
            lt_of_le_of_ne hs.2 (fun h => hne (Or.inr ⟨h, rfl⟩))⟩, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          refine ⟨⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩, ?_⟩
          intro h
          rcases (heq s ⟨hs.1.le, hs.2.le⟩).mp h with h | ⟨h, -⟩
          · exact hs.1.ne' h
          · exact hs.2.ne h
      rw [himage]
      exact (isConnected_Ioo hab).image f (hf.mono Ioo_subset_Icc_self)
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      have himage : f '' Icc a b \ {f t} = f '' Ico a t ∪ f '' Ioc t b := by
        ext x
        constructor
        · rintro ⟨⟨s, hs, rfl⟩, hsf⟩
          have hst : s ≠ t := fun h => hsf (congrArg f h)
          rcases lt_or_gt_of_ne hst with hst | hts
          · exact Or.inl ⟨s, ⟨hs.1, hst⟩, rfl⟩
          · exact Or.inr ⟨s, ⟨hts, hs.2⟩, rfl⟩
        · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
          · have hs' : s ∈ Icc a b := ⟨hs.1, (hs.2.trans ht.2).le⟩
            refine ⟨⟨s, hs', rfl⟩, fun h => ?_⟩
            rcases (heq s hs').mp h with h | ⟨-, h⟩
            · exact hs.2.ne h
            · exact hta h
          · have hs' : s ∈ Icc a b := ⟨(ht.1.trans hs.1.le), hs.2⟩
            refine ⟨⟨s, hs', rfl⟩, fun h => ?_⟩
            rcases (heq s hs').mp h with h | ⟨-, h⟩
            · exact hs.1.ne' h
            · exact hta h
      rw [himage]
      have hleft := (isConnected_Ico hat).image f (hf.mono (fun s hs => ⟨hs.1, (hs.2.trans ht.2).le⟩))
      have hright := (isConnected_Ioc ht.2).image f (hf.mono (fun s hs => ⟨ht.1.trans hs.1.le, hs.2⟩))
      exact IsConnected.union ⟨f a, ⟨a, ⟨le_rfl, hat⟩, rfl⟩, b, ⟨ht.2, le_rfl⟩, hclose.symm⟩ hleft hright
  · have heq : f '' Icc a b \ {p} = f '' Icc a b :=
      sdiff_eq_left.mpr (disjoint_singleton_right.mpr hp)
    rw [heq]
    exact (isConnected_Icc hab.le).image f hf

end DifferentialGeometry.Topology
