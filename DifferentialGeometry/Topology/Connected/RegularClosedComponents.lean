import DifferentialGeometry.Topology.Connected.ComponentIn
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {K : Set X}

private theorem closure_interior_image_of_isClopen
    (hK : closure (interior K) = K) {C : Set K} (hC : IsClopen C) :
    closure (interior (Subtype.val '' C : Set X)) = Subtype.val '' C := by
  have hclosed : IsClosed K := hK ▸ isClosed_closure
  have hCclosed : IsClosed (Subtype.val '' C : Set X) :=
    hclosed.isClosedMap_subtype_val C hC.isClosed
  obtain ⟨U, hU, hCU⟩ := hC.isOpen.image_val
  apply Subset.antisymm (closure_minimal interior_subset hCclosed)
  intro x hx
  rw [hCU] at hx
  have hxcl : x ∈ closure (U ∩ interior K) :=
    hU.inter_closure ⟨hx.1, hK.symm ▸ hx.2⟩
  apply closure_mono ?_ hxcl
  apply interior_maximal ?_ (hU.inter isOpen_interior)
  intro y hy
  rw [hCU]
  exact ⟨hy.1, interior_subset hy.2⟩

theorem closure_interior_connectedComponentIn [LocallyConnectedSpace K]
    (hK : closure (interior K) = K) (x : X) :
    closure (interior (connectedComponentIn K x)) = connectedComponentIn K x := by
  by_cases hx : x ∈ K
  · rw [connectedComponentIn_eq_image hx]
    exact closure_interior_image_of_isClopen hK isClopen_connectedComponent
  · rw [connectedComponentIn_eq_empty hx, interior_empty, closure_empty]

theorem isCompact_connectedComponentIn (hK : IsCompact K) (x : X) :
    IsCompact (connectedComponentIn K x) := by
  by_cases hx : x ∈ K
  · let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [connectedComponentIn_eq_image hx]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

theorem frontier_connectedComponentIn_subset [LocallyConnectedSpace X] (K : Set X) (x : X) :
    frontier (connectedComponentIn K x) ⊆ frontier K := by
  intro y hy
  refine ⟨closure_mono (connectedComponentIn_subset K x) hy.1, ?_⟩
  intro hyint
  have hyC : y ∈ connectedComponentIn K x := by
    rw [← closure_connectedComponentIn_inter K x]
    exact ⟨hy.1, interior_subset hyint⟩
  have hsub : connectedComponentIn (interior K) y ⊆ connectedComponentIn K x := by
    rw [connectedComponentIn_eq hyC]
    exact connectedComponentIn_mono y interior_subset
  have hopen : IsOpen (connectedComponentIn (interior K) y) :=
    isOpen_interior.connectedComponentIn
  exact hy.2 ((interior_maximal hsub hopen) (mem_connectedComponentIn hyint))

theorem frontier_connectedComponentIn_eq_iUnion [LocallyConnectedSpace X]
    (hK : IsClosed K) {ι : Type*} (F : ι → Set X)
    (hF : ∀ i, IsPreconnected (F i)) (hfront : frontier K = ⋃ i, F i)
    (x : X) :
    frontier (connectedComponentIn K x) =
      ⋃ i, ⋃ (_ : (F i ∩ connectedComponentIn K x).Nonempty), F i := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨i, hyF⟩ := mem_iUnion.mp
      (hfront ▸ frontier_connectedComponentIn_subset K x hy)
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨y, hyF,
      (hK.connectedComponentIn x).frontier_subset hy⟩, hyF⟩⟩
  · intro y hy
    obtain ⟨i, hy⟩ := mem_iUnion.mp hy
    obtain ⟨⟨z, hzF, hzC⟩, hyF⟩ := mem_iUnion.mp hy
    have hsub : F i ⊆ K := by
      intro w hw
      exact hK.frontier_subset (hfront.symm ▸ mem_iUnion.mpr ⟨i, hw⟩)
    have hFC : F i ⊆ connectedComponentIn K x := by
      rw [connectedComponentIn_eq hzC]
      exact (hF i).subset_connectedComponentIn hzF hsub
    refine ⟨subset_closure (hFC hyF), ?_⟩
    intro hyint
    have hyfront : y ∈ frontier K := hfront.symm ▸ mem_iUnion.mpr ⟨i, hyF⟩
    exact hyfront.2 (interior_mono (connectedComponentIn_subset K x) hyint)

end DifferentialGeometry.Topology
