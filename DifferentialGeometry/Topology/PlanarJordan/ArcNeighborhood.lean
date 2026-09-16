import DifferentialGeometry.External.Schoenflies.MatchedArc

open Set Topology

namespace Schoenflies

theorem IsArcBetween.mem_nhdsWithin_of_subarc {A B : Set Plane} {p q r : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p r) (hBA : B ⊆ A) :
    B ∈ 𝓝[A] p := by
  obtain ⟨f, hfc, hfi, hfA, hf0, _⟩ := hA
  obtain ⟨t, ht, hft⟩ := hfA.symm ▸ hBA hB.right_mem
  have hpr : p ≠ r := by
    obtain ⟨g, _, hgi, _, hg0, hg1⟩ := hB
    exact fun h => zero_ne_one (hgi zero_mem_I one_mem_I (hg0.trans (h.trans hg1.symm)))
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (fun heq => hpr (hf0.symm.trans (heq ▸ hft)))
  have hsub : f '' Icc 0 t ⊆ A := by
    rw [← hfA]
    exact image_mono (Icc_subset_Icc le_rfl ht.2)
  have harc : IsArcBetween (f '' Icc 0 t) p r := by
    simpa only [uIcc_of_le htpos.le, hf0, hft] using
      isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I ht htpos.ne
  have heq := hB.eq_of_subset_arc harc ⟨f, hfc, hfi, hfA, hf0, rfl⟩ hBA hsub
  obtain ⟨ε, hε, hball⟩ := exists_ball_inter_subset_image hfc hfi
    (U := Iio t) isOpen_Iio ⟨0, ⟨htpos, zero_mem_I⟩, hf0⟩
  apply Filter.mem_of_superset (inter_mem_nhdsWithin A (Metric.ball_mem_nhds p hε))
  intro x hx
  rw [heq]
  obtain ⟨s, hs, rfl⟩ := hball ⟨hx.2, hfA.symm ▸ hx.1⟩
  exact mem_image_of_mem f ⟨hs.2.1, hs.1.le⟩

end Schoenflies
