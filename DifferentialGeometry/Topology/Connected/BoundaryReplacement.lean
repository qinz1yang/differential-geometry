/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Connected.SeparatorLocation

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem frontier_sdiff_subset_of_local_separation {S C N U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : U ∪ V = Sᶜ)
    (hSV : S ∩ N ⊆ closure V) (hN : closure (interior N) = N)
    (hNU : interior N ⊆ U) (hC : IsClosed C) (hout : S \ N ⊆ C)
    (hfront : frontier N ⊆ S ∪ C)
    (hlocal : ∀ x ∈ S ∩ N, ∀ W ∈ 𝓝 x, ∃ O ∈ 𝓝 x, O ⊆ W ∧
      ∃ A B : Set X, IsPreconnected A ∧ IsPreconnected B ∧ A ∪ B = O \ S) :
    frontier (U \ N) ⊆ C := by
  have hNclosed : IsClosed N := hN ▸ isClosed_closure
  have hWopen : IsOpen (U \ N) := hU.sdiff hNclosed
  have hUS : U ⊆ Sᶜ := subset_union_left.trans hcover.subset
  have hVS : V ⊆ Sᶜ := subset_union_right.trans hcover.subset
  have hUV : closure U ⊆ Vᶜ :=
    closure_minimal (disjoint_left.mp hdis) hV.isClosed_compl
  have hWN : closure (U \ N) ⊆ (interior N)ᶜ :=
    closure_minimal (fun _ hx hy => hx.2 (interior_subset hy))
      isOpen_interior.isClosed_compl
  intro x hx
  by_contra hxC
  have hxcl : x ∈ closure (U \ N) := hx.1
  have hxUcl : x ∈ closure U := closure_mono sdiff_subset hxcl
  have hxnot : x ∉ U \ N := by simpa only [hWopen.interior_eq] using hx.2
  by_cases hxN : x ∈ N
  · have hxS : x ∈ S := (hfront ⟨subset_closure hxN, hWN hxcl⟩).resolve_right hxC
    obtain ⟨O, hO, hOC, A, B, hA, hB, hAB⟩ :=
      hlocal x ⟨hxS, hxN⟩ Cᶜ (hC.isOpen_compl.mem_nhds hxC)
    obtain ⟨u, huO, huN⟩ :=
      (mem_closure_iff_nhds.mp (hN.symm ▸ hxN)) O hO
    obtain ⟨v, hvO, hvV⟩ := (mem_closure_iff_nhds.mp (hSV ⟨hxS, hxN⟩)) O hO
    have huU : u ∈ U := hNU huN
    have huAB : u ∈ A ∪ B := hAB.symm.subset ⟨huO, hUS huU⟩
    have finish (A B : Set X) (hA : IsPreconnected A) (hB : IsPreconnected B)
        (hAB : A ∪ B = O \ S) (huA : u ∈ A) : False := by
      have hAS : A ⊆ O \ S := subset_union_left.trans hAB.subset
      have hBS : B ⊆ O \ S := subset_union_right.trans hAB.subset
      have hAU : A ⊆ U := hA.subset_left_of_subset_union hU hV hdis
        (fun y hy => hcover.symm.subset (hAS hy).2) ⟨u, huA, huU⟩
      have hvB : v ∈ B := (hAB.symm.subset ⟨hvO, hVS hvV⟩).resolve_left
        (fun hvA => disjoint_left.mp hdis (hAU hvA) hvV)
      have hBV : B ⊆ V := hB.subset_left_of_subset_union hV hU hdis.symm
        (fun y hy => by simpa only [union_comm] using hcover.symm.subset (hBS hy).2)
        ⟨v, hvB, hvV⟩
      have hAN : A ⊆ interior N := hA.subset_left_of_subset_union isOpen_interior
        hNclosed.isOpen_compl (disjoint_compl_right.mono interior_subset (Subset.refl _))
        (by
          intro y hy
          by_cases hyN : y ∈ N
          · left
            apply (mem_interior_iff_notMem_frontier hyN).2
            intro hyfront
            rcases hfront hyfront with hyS | hyC
            · exact (hAS hy).2 hyS
            · exact hOC (hAS hy).1 hyC
          · exact Or.inr hyN) ⟨u, huA, huN⟩
      obtain ⟨y, hyO, hyU, hyN⟩ := (mem_closure_iff_nhds.mp hxcl) O hO
      rcases hAB.symm.subset ⟨hyO, hUS hyU⟩ with hyA | hyB
      · exact hyN (interior_subset (hAN hyA))
      · exact disjoint_left.mp hdis hyU (hBV hyB)
    rcases huAB with huA | huB
    · exact finish A B hA hB hAB huA
    · exact finish B A hB hA (by simpa only [union_comm] using hAB) huB
  · have hxnotU : x ∉ U := fun hxU => hxnot ⟨hxU, hxN⟩
    have hxS : x ∈ S := by
      by_contra hxS
      rcases hcover.symm.subset hxS with hxU | hxV
      · exact hxnotU hxU
      · exact hUV hxUcl hxV
    exact hxC (hout ⟨hxS, hxN⟩)

end DifferentialGeometry.Topology
