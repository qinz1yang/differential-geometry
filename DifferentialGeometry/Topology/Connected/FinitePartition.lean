import DifferentialGeometry.Topology.Connected.TwoComponentPartition

open Set

namespace DifferentialGeometry.Topology

theorem existsUnique_subset_of_isConnected_of_finite_closed_partition
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    {C : Set (Set X)} (hC : C.Finite) (hclosed : ∀ T ∈ C, IsClosed T)
    (hdisjoint : C.PairwiseDisjoint id) (hcover : S ⊆ ⋃₀ C) :
    ∃! T, T ∈ C ∧ S ⊆ T := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨T, hTC, hxT⟩ := mem_sUnion.mp (hcover hx)
  let R : Set X := ⋃ U ∈ C \ {T}, U
  have hRclosed : IsClosed R := by
    have hfinite : (C \ {T}).Finite := hC.subset sdiff_subset
    exact hfinite.isClosed_biUnion (fun U hU => hclosed U hU.1)
  have hTR : Disjoint T R := by
    apply Set.disjoint_left.mpr
    intro y hyT hyR
    obtain ⟨U, hU, hyU⟩ := mem_iUnion₂.mp hyR
    exact Set.disjoint_left.mp (hdisjoint hTC hU.1 (Ne.symm hU.2)) hyT hyU
  have hcover' : S ⊆ T ∪ R := by
    intro y hy
    obtain ⟨U, hUC, hyU⟩ := mem_sUnion.mp (hcover hy)
    by_cases hUT : U = T
    · exact Or.inl (hUT ▸ hyU)
    · exact Or.inr (mem_iUnion₂.mpr ⟨U, ⟨hUC, hUT⟩, hyU⟩)
  have hST : S ⊆ T := by
    rcases subset_or_subset_of_isPreconnected_of_isClosed hS.isPreconnected
      (hclosed T hTC) hRclosed hTR hcover' with h | h
    · exact h
    · exact (Set.disjoint_left.mp hTR hxT (h hx)).elim
  refine ⟨T, ⟨hTC, hST⟩, ?_⟩
  intro U hU
  by_contra hUT
  exact Set.disjoint_left.mp (hdisjoint hU.1 hTC hUT) (hU.2 hx) hxT

end DifferentialGeometry.Topology
