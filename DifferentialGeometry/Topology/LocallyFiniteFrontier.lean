/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Compactness.LocallyFinite

open Set Topology

namespace DifferentialGeometry.Topology

theorem eventually_mem_frontier_iUnion_iff_pair_of_finite_neighborhood
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} (hF : ∀ i, IsClosed (F i))
    {x : X} {O : Set X} (hO : IsOpen O) (hxO : x ∈ O)
    (hfin : {i | (F i ∩ O).Nonempty}.Finite) (i j : ι)
    (hother : ∀ k, k ≠ i → k ≠ j → x ∉ F k) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (⋃ k, F k) ↔ y ∈ frontier (F i ∪ F j) := by
  let I : Set ι := {k | (F k ∩ O).Nonempty ∧ k ≠ i ∧ k ≠ j}
  have hIfin : I.Finite := hfin.subset fun _ hk => hk.1
  have hclosed : IsClosed (⋃ k ∈ I, F k) := hIfin.isClosed_biUnion fun k _ => hF k
  let W := O ∩ (⋃ k ∈ I, F k)ᶜ
  have hW : IsOpen W := hO.inter hclosed.isOpen_compl
  have hxW : x ∈ W := by
    refine ⟨hxO, ?_⟩
    intro hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    exact hother k hk.2.1 hk.2.2 hxk
  have heq : (⋃ k, F k) ∩ W = (F i ∪ F j) ∩ W := by
    ext y
    constructor
    · rintro ⟨hy, hyW⟩
      obtain ⟨k, hyk⟩ := mem_iUnion.mp hy
      refine ⟨?_, hyW⟩
      by_cases hki : k = i
      · exact Or.inl (hki ▸ hyk)
      by_cases hkj : k = j
      · exact Or.inr (hkj ▸ hyk)
      exact (hyW.2 (mem_iUnion₂.mpr ⟨k, ⟨⟨y, hyk, hyW.1⟩, hki, hkj⟩, hyk⟩)).elim
    · rintro ⟨hy, hyW⟩
      exact ⟨hy.elim (fun h => subset_iUnion F i h) (fun h => subset_iUnion F j h), hyW⟩
  have hfr : frontier (⋃ k, F k) ∩ W = frontier (F i ∪ F j) ∩ W := by
    rw [← frontier_inter_open_inter hW, heq, frontier_inter_open_inter hW]
  filter_upwards [hW.mem_nhds hxW] with y hy
  exact ⟨fun h => (hfr.subset ⟨h, hy⟩).1, fun h => (hfr.symm.subset ⟨h, hy⟩).1⟩

end DifferentialGeometry.Topology
