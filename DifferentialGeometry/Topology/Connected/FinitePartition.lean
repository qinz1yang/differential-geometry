import DifferentialGeometry.Topology.Connected.FiniteClosedCover

open Set

namespace DifferentialGeometry.Topology

theorem existsUnique_subset_of_isConnected_of_finite_closed_partition
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    {C : Set (Set X)} (hC : C.Finite) (hclosed : ∀ T ∈ C, IsClosed T)
    (hdisjoint : C.PairwiseDisjoint id) (hcover : S ⊆ ⋃₀ C) :
    ∃! T, T ∈ C ∧ S ⊆ T := by
  let _ : Finite C := hC.to_subtype
  have hdisj : Pairwise (fun T U : C => Disjoint (T : Set X) U) := by
    intro T U hTU
    exact hdisjoint T.property U.property (fun h => hTU (Subtype.ext h))
  have hcover' : S ⊆ ⋃ T : C, (T : Set X) := by
    intro x hx
    obtain ⟨T, hTC, hxT⟩ := mem_sUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨T, hTC⟩, hxT⟩
  obtain ⟨T, hST, hunique⟩ := hS.exists_unique_subset_of_iUnion_disjoint_closed
    (fun T : C => hclosed T T.property) hdisj hcover'
  refine ⟨T, ⟨T.property, hST⟩, ?_⟩
  intro U hU
  exact congrArg Subtype.val (hunique ⟨U, hU.1⟩ hU.2)

end DifferentialGeometry.Topology
