import DifferentialGeometry.Topology.PlanarJordan.ArcChainLimit
import DifferentialGeometry.Topology.PlanarJordan.EndpointCollarChain

open Set Filter Topology

namespace Schoenflies

open DifferentialGeometry.Topology.PlanarJordan

theorem IsArcBetween.exists_isArcBetween_inter_eq_singleton
    {A : Set Plane} {p q : Plane} (hA : IsArcBetween A p q)
    {U : Set Plane} (hU : U ∈ 𝓝 p) :
    ∃ (B : Set Plane) (r : Plane), IsArcBetween B p r ∧ B ⊆ U ∧ B ∩ A = {p} := by
  obtain ⟨f, hf, hi, himage, hf0, _⟩ := hA
  obtain ⟨O, hO, hmeet, hdis, hlim⟩ :=
    exists_shrinking_open_chain_compl_arc hf hi (hf0.symm ▸ hU)
  obtain ⟨z, B, hB, hBmeet, hBdis, _⟩ :=
    exists_polygonal_arc_chain_of_isOpen_isConnected (fun n => (hO n).1)
      (fun n => (hO n).2.1) hmeet hdis
  have havoid (n : ℕ) : Disjoint (B n) (f '' unitInterval) :=
    disjoint_left.mpr fun x hx => ((hO (n + 1)).2.2 ((hB n).2.2.2 hx)).2
  have hq (n : ℕ) : f 0 ∉ B n := fun hx =>
    disjoint_left.mp (havoid n) hx (mem_image_of_mem f zero_mem_I)
  have hBlim : Tendsto B atTop (𝓝 (f 0)).smallSets :=
    (hlim.comp (tendsto_add_atTop_nat 1)).smallSets_mono
      (Eventually.of_forall fun n => (hB n).2.2.2)
  have hC := isArcBetween_insert_iUnion_of_tendsto (fun n => (hB n).2.1) hBmeet hBdis hq hBlim
  refine ⟨insert (f 0) (⋃ n, B n), z 0, hf0 ▸ hC, ?_, ?_⟩
  · rintro x (rfl | hx)
    · exact hf0.symm ▸ mem_of_mem_nhds hU
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ((hO (n + 1)).2.2 ((hB n).2.2.2 hn)).1
  · apply Subset.antisymm
    · rintro x ⟨hx, hxA⟩
      rcases hx with hx | hx
      · exact hx.trans hf0
      · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        exact False.elim (disjoint_left.mp (havoid n) hn (himage.symm ▸ hxA))
    · apply singleton_subset_iff.mpr
      exact ⟨Or.inl hf0.symm, hf0 ▸ himage.subset (mem_image_of_mem f zero_mem_I)⟩

end Schoenflies
