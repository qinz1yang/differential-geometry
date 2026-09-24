import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Closure
import Mathlib.Data.Finite.Defs

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology

theorem isCompact_compl_iUnion_of_compact_remainders
    {M ι : Type*} [TopologicalSpace M] [Finite ι]
    (K : Set M) (hK : IsCompact K) (U E : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hboundary : ∀ i, IsCompact (E i \ U i))
    (hcover : K ∪ ⋃ i, E i = univ) : IsCompact (⋃ i, U i)ᶜ := by
  have hclosed : IsClosed (⋃ i, U i)ᶜ := (isOpen_iUnion hU).isClosed_compl
  apply IsCompact.of_isClosed_subset (hK.union (isCompact_iUnion hboundary)) hclosed
  intro x hx
  have hxfull : x ∈ K ∪ ⋃ i, E i := hcover.symm ▸ mem_univ x
  rcases hxfull with hxK | hxE
  · exact Or.inl hxK
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
    exact Or.inr (mem_iUnion.mpr ⟨i, hxi, fun h => hx (mem_iUnion.mpr ⟨i, h⟩)⟩)

theorem compl_iUnion_inter_of_pairwise_disjoint
    {M ι : Type*} (U E : ι → Set M)
    (hsub : ∀ i, U i ⊆ E i) (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (i : ι) :
    (⋃ j, U j)ᶜ ∩ E i = E i \ U i := by
  classical
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, fun h => hx.1 (mem_iUnion.mpr ⟨i, h⟩)⟩
  · intro hx
    refine ⟨?_, hx.1⟩
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    by_cases hji : j = i
    · exact hx.2 (hji ▸ hj)
    · exact disjoint_left.mp (hdis hji) (hsub j hj) hx.1

theorem frontier_compl_iUnion_of_finite_disjoint_closures
    {M ι : Type*} [TopologicalSpace M] [Finite ι]
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hdis : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j)))) :
    frontier (⋃ i, U i)ᶜ = ⋃ i, closure (U i) \ U i := by
  rw [frontier_compl, frontier, (isOpen_iUnion hU).interior_eq, closure_iUnion_of_finite]
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    exact mem_iUnion.mpr ⟨i, hi, fun h => hx.2 (mem_iUnion.mpr ⟨i, h⟩)⟩
  · intro hx
    obtain ⟨i, hxi, hxni⟩ := mem_iUnion.mp hx
    refine ⟨mem_iUnion.mpr ⟨i, hxi⟩, ?_⟩
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    by_cases hji : j = i
    · exact hxni (hji ▸ hj)
    · exact disjoint_left.mp (hdis hji) (subset_closure hj) hxi

end DifferentialGeometry.Topology
