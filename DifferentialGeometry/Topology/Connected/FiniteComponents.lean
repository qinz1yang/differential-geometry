import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

open Set

namespace DifferentialGeometry.Topology

theorem exists_finite_isConnected_partition {X ι : Type*} [TopologicalSpace X]
    (d : Finset ι) (A : ι → Set X) (hcompact : ∀ i ∈ d, IsCompact (A i))
    (hconn : ∀ i ∈ d, IsConnected (A i)) :
    ∃ C : Set (Set X), C.Finite ∧ C.PairwiseDisjoint id ∧
      (∀ B ∈ C, IsCompact B ∧ IsConnected B ∧ ∃ i ∈ d, A i ⊆ B) ∧
      ⋃₀ C = ⋃ i ∈ d, A i := by
  classical
  let U := ⋃ i ∈ d, A i
  let I := {i : ι // i ∈ d}
  let _ : Finite I := d.finite_toSet.to_subtype
  let p : I → X := fun i => Classical.choose (hconn i.1 i.2).nonempty
  have hp : ∀ i : I, p i ∈ A i.1 := fun i => Classical.choose_spec (hconn i.1 i.2).nonempty
  have hAU : ∀ i ∈ d, A i ⊆ U := by
    intro i hi x hx
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx⟩⟩
  have hU : IsCompact U := d.finite_toSet.isCompact_biUnion hcompact
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let B : I → Set X := fun i => connectedComponentIn U (p i)
  have hAB : ∀ i : I, A i.1 ⊆ B i := fun i =>
    (hconn i.1 i.2).isPreconnected.subset_connectedComponentIn (hp i) (hAU i.1 i.2)
  have hBU : ∀ i : I, B i ⊆ U := fun i => connectedComponentIn_subset U (p i)
  refine ⟨range B, finite_range B, ?_, ?_, ?_⟩
  · rintro S ⟨i, rfl⟩ T ⟨j, rfl⟩ hne
    apply disjoint_left.mpr
    intro x hxi hxj
    exact hne ((connectedComponentIn_eq hxi).trans (connectedComponentIn_eq hxj).symm)
  · rintro S ⟨i, rfl⟩
    have hpi : p i ∈ U := hAU i.1 i.2 (hp i)
    refine ⟨?_, isConnected_connectedComponentIn_iff.mpr hpi, i.1, i.2, hAB i⟩
    change IsCompact (connectedComponentIn U (p i))
    rw [connectedComponentIn_eq_image hpi]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · apply Subset.antisymm
    · rintro x ⟨S, ⟨i, rfl⟩, hx⟩
      exact hBU i hx
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_sUnion.mpr ⟨B ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, hAB ⟨i, hi⟩ hxi⟩

end DifferentialGeometry.Topology
