/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.BicollarLocalSide
import DifferentialGeometry.Topology.Connected.Separation

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

private theorem exterior_partition_neighborhood {M R N U V : Set X}
    (hR : IsClosed R) (hN : IsClosed N) (hreg : N ⊆ closure (interior N))
    (hbi : IsBicollared (frontier N)) (hout : M \ N = R \ N)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : U ∪ V = Mᶜ)
    {y : X} (hy : y ∈ frontier N \ R) (hyA : y ∈ closure (U \ N)) :
    ∃ O ∈ 𝓝 y, O ⊆ Rᶜ ∧ O \ N ⊆ U := by
  let _ : LocallyConnectedSpace (frontier N) := hbi.locallyConnectedSpace
  let A := closure (U \ N)
  have hAV : A ⊆ Vᶜ := closure_minimal
    (fun _ hx => disjoint_left.mp hdis hx.1) hV.isClosed_compl
  have hAN : A ⊆ (interior N)ᶜ := by
    apply closure_minimal (fun _ hx => fun hn => hx.2 (interior_subset hn))
      isOpen_interior.isClosed_compl
  have hfront : Rᶜ ∩ frontier A ⊆ N := by
    intro z hz
    by_contra hzN
    have hzM : z ∉ M := fun hm => hz.1 ((hout.subset ⟨hm, hzN⟩).1)
    rcases hcover.symm.subset hzM with hzU | hzV
    · exact hz.2.2 ((hU.sdiff hN).subset_interior_closure ⟨hzU, hzN⟩)
    · exact hAV (isClosed_closure.frontier_subset hz.2) hzV
  have hint : Disjoint (interior A) (interior N) :=
    disjoint_left.mpr fun _ hx => hAN (interior_subset hx)
  have hyAi : y ∈ closure (interior A) :=
    closure_mono (hU.sdiff hN).subset_interior_closure hyA
  obtain ⟨O, hO, -, hside⟩ := hbi.exists_mem_nhds_of_inter_frontier_subset hN
    isClosed_closure hreg hR.isOpen_compl hfront hint hy.2 hyAi hy.1
  refine ⟨O ∩ Rᶜ, Filter.inter_mem hO (hR.isOpen_compl.mem_nhds hy.2),
    inter_subset_right, ?_⟩
  intro z hz
  have hzM : z ∉ M := fun hm => hz.1.2 ((hout.subset ⟨hm, hz.2⟩).1)
  exact (hcover.symm.subset hzM).resolve_right
    (hAV (interior_subset (hside ⟨hz.1.1, hz.2⟩)))

theorem Separates.of_bicollared_frontier_replacement {M R N H K : Set X}
    (h : Separates M H K) (hR : IsClosed R) (hN : IsClosed N)
    (hreg : N ⊆ closure (interior N)) (hbi : IsBicollared (frontier N))
    (hpatch : IsPreconnected (frontier N \ R)) (hout : M \ N = R \ N)
    (hHN : H ⊆ Nᶜ) (hKN : K ⊆ Nᶜ) : Separates R H K := by
  obtain ⟨U, V, hU, hV, hdis, hcover, hHU, hKV⟩ := h
  let A := closure (U \ N)
  let B := closure (V \ N)
  have hpatchCover : frontier N \ R ⊆ A ∪ B := by
    intro y hy
    have hycl : y ∈ closure Nᶜ := by
      simpa only [closure_compl, mem_compl_iff] using hy.1.2
    have hc : y ∈ closure ((U \ N) ∪ (V \ N)) := by
      apply mem_closure_iff.mpr
      intro O hO hyO
      obtain ⟨z, hzO, hzN⟩ := mem_closure_iff.mp hycl (O ∩ Rᶜ)
        (hO.inter hR.isOpen_compl) ⟨hyO, hy.2⟩
      have hzM : z ∉ M := fun hm => hzO.2 ((hout.subset ⟨hm, hzN⟩).1)
      refine ⟨z, hzO.1, ?_⟩
      exact (hcover.symm.subset hzM).elim
        (fun hz => Or.inl ⟨hz, hzN⟩) (fun hz => Or.inr ⟨hz, hzN⟩)
    simpa only [closure_union] using hc
  have hnoBoth : ∀ y ∈ frontier N \ R, y ∈ A → y ∈ B → False := by
    intro y hy hyA hyB
    obtain ⟨O, hO, -, hside⟩ := exterior_partition_neighborhood hR hN hreg hbi hout
      hU hV hdis hcover hy hyA
    obtain ⟨O', hO'sub, hO'open, hyO'⟩ := mem_nhds_iff.mp hO
    obtain ⟨z, hzO', hzV, hzN⟩ := mem_closure_iff.mp hyB O' hO'open hyO'
    exact disjoint_left.mp hdis (hside ⟨hO'sub hzO', hzN⟩) hzV
  have hcases : frontier N \ R ⊆ A ∨ frontier N \ R ⊆ B := by
    by_cases hA : frontier N \ R ⊆ A
    · exact Or.inl hA
    · right
      by_contra hB
      obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hA
      obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hB
      obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.mp hpatch A B
        isClosed_closure isClosed_closure hpatchCover
        ⟨y, hy, (hpatchCover hy).resolve_right hyB⟩
        ⟨x, hx, (hpatchCover hx).resolve_left hxA⟩
      exact hnoBoth z hz hzA hzB
  have key : ∀ U V H K : Set X, IsOpen U → IsOpen V → Disjoint U V → U ∪ V = Mᶜ →
      H ⊆ U → K ⊆ V → H ⊆ Nᶜ → K ⊆ Nᶜ →
      frontier N \ R ⊆ closure (U \ N) → Separates R H K := by
    intro U V H K hU hV hdis hcover hHU hKV hHN hKN hA
    let U' := (U \ N) ∪ (N \ R)
    let V' := V \ N
    have hU' : IsOpen U' := by
      apply isOpen_iff_mem_nhds.mpr
      intro y hy
      rcases hy with hy | hy
      · exact Filter.mem_of_superset ((hU.sdiff hN).mem_nhds hy) subset_union_left
      · by_cases hyi : y ∈ interior N
        · apply Filter.mem_of_superset ((isOpen_interior.sdiff hR).mem_nhds ⟨hyi, hy.2⟩)
          exact fun _ hx => Or.inr ⟨interior_subset hx.1, hx.2⟩
        · have hyfr : y ∈ frontier N :=
            (mem_frontier_iff_notMem_interior hy.1).mpr hyi
          obtain ⟨O, hO, hOR, hside⟩ := exterior_partition_neighborhood hR hN hreg hbi hout
            hU hV hdis hcover ⟨hyfr, hy.2⟩ (hA ⟨hyfr, hy.2⟩)
          apply Filter.mem_of_superset hO
          intro z hz
          by_cases hzN : z ∈ N
          · exact Or.inr ⟨hzN, hOR hz⟩
          · exact Or.inl ⟨hside ⟨hz, hzN⟩, hzN⟩
    have hdis' : Disjoint U' V' := by
      apply disjoint_left.mpr
      rintro z (hzU | hzN) hzV
      · exact disjoint_left.mp hdis hzU.1 hzV.1
      · exact hzV.2 hzN.1
    have hUC : U ⊆ Mᶜ := subset_union_left.trans hcover.subset
    have hVC : V ⊆ Mᶜ := subset_union_right.trans hcover.subset
    have hcover' : U' ∪ V' = Rᶜ := by
      apply Subset.antisymm
      · rintro z ((hzU | hzN) | hzV) hzR
        · exact hUC hzU.1 ((hout.symm.subset ⟨hzR, hzU.2⟩).1)
        · exact hzN.2 hzR
        · exact hVC hzV.1 ((hout.symm.subset ⟨hzR, hzV.2⟩).1)
      · intro z hzR
        by_cases hzN : z ∈ N
        · exact Or.inl (Or.inr ⟨hzN, hzR⟩)
        · have hzM : z ∉ M := fun hm => hzR ((hout.subset ⟨hm, hzN⟩).1)
          rcases hcover.symm.subset hzM with hzU | hzV
          · exact Or.inl (Or.inl ⟨hzU, hzN⟩)
          · exact Or.inr ⟨hzV, hzN⟩
    exact ⟨U', V', hU', hV.sdiff hN, hdis', hcover',
      fun z hz => Or.inl ⟨hHU hz, hHN hz⟩, fun z hz => ⟨hKV hz, hKN hz⟩⟩
  rcases hcases with hA | hB
  · exact key U V H K hU hV hdis hcover hHU hKV hHN hKN hA
  · exact (key V U K H hV hU hdis.symm ((union_comm V U).trans hcover)
      hKV hHU hKN hHN hB).symm

end DifferentialGeometry.Topology
