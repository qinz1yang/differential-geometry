import DifferentialGeometry.External.Schoenflies.Subarc
import Mathlib.Topology.Order.Compact

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_isArcBetween_sdiff_pair_subset_compl
    {A F : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hF : IsClosed F)
    (hp : p ∈ F) (hq : q ∈ F) (hne : ¬A ⊆ F) :
    ∃ (B : Set Schoenflies.Plane) (a b : Schoenflies.Plane),
      Schoenflies.IsArcBetween B a b ∧ B ⊆ A ∧ a ∈ F ∧ b ∈ F ∧ B \ {a, b} ⊆ Fᶜ := by
  obtain ⟨f, hc, hi, hfA, hf0, hf1⟩ := hA
  obtain ⟨x, hxA, hxF⟩ := Set.not_subset.mp hne
  obtain ⟨t, ht, rfl⟩ := hfA.symm ▸ hxA
  have hleft : IsCompact (Icc 0 t ∩ f ⁻¹' F) :=
    isCompact_Icc.of_isClosed_subset
      ((hc.mono (Icc_subset_Icc_right ht.2)).preimage_isClosed_of_isClosed isClosed_Icc hF)
      inter_subset_left
  have hright : IsCompact (Icc t 1 ∩ f ⁻¹' F) :=
    isCompact_Icc.of_isClosed_subset
      ((hc.mono (Icc_subset_Icc_left ht.1)).preimage_isClosed_of_isClosed isClosed_Icc hF)
      inter_subset_left
  obtain ⟨a, ha, hmax⟩ := hleft.exists_isGreatest ⟨0, ⟨le_rfl, ht.1⟩, by simpa using hf0.symm ▸ hp⟩
  obtain ⟨b, hb, hmin⟩ := hright.exists_isLeast ⟨1, ⟨ht.2, le_rfl⟩, by simpa using hf1.symm ▸ hq⟩
  have hat : a < t := lt_of_le_of_ne ha.1.2 (fun heq => hxF (heq ▸ ha.2))
  have htb : t < b := lt_of_le_of_ne hb.1.1 (fun heq => hxF (heq.symm ▸ hb.2))
  have hab : a < b := hat.trans htb
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.1, ha.1.2.trans ht.2⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hb.1.1, hb.1.2⟩
  have hBI : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc haI.1 hbI.2
  have hB : Schoenflies.IsArcBetween (f '' Icc a b) (f a) (f b) := by
    simpa only [uIcc_of_le hab.le] using Schoenflies.isArcBetween_subarc_of_injOn_I
      hc hi haI hbI hab.ne
  refine ⟨f '' Icc a b, f a, f b, hB, (image_mono hBI).trans hfA.subset, ha.2, hb.2, ?_⟩
  rintro y ⟨⟨u, hu, rfl⟩, hends⟩ huF
  have hau : a < u := lt_of_le_of_ne hu.1 (fun heq => hends (Or.inl (congrArg f heq.symm)))
  have hub : u < b := lt_of_le_of_ne hu.2 (fun heq => hends (Or.inr (congrArg f heq)))
  rcases le_total u t with hut | htu
  · exact (not_le_of_gt hau) (hmax ⟨⟨ha.1.1.trans hu.1, hut⟩, huF⟩)
  · exact (not_le_of_gt hub) (hmin ⟨⟨htu, hu.2.trans hb.1.2⟩, huF⟩)

end DifferentialGeometry.Topology.PlanarJordan
