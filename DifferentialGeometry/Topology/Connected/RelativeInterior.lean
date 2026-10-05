import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.LocallyConnected

open Set

namespace DifferentialGeometry.Topology

theorem mem_interior_image_val_of_isOpen
    {M : Type*} [TopologicalSpace M] {s : Set M} {V : Set s}
    (hV : IsOpen V) {x : s} (hxV : x ∈ V) (hxs : x.val ∈ interior s) :
    x.val ∈ interior ((Subtype.val : s → M) '' V) := by
  obtain ⟨W, hW, hWV⟩ := hV.image_val
  have hxW : x.val ∈ W := by
    have hx : x.val ∈ (Subtype.val : s → M) '' V := ⟨x, hxV, rfl⟩
    rw [hWV] at hx
    exact hx.1
  rw [hWV, interior_inter, hW.interior_eq]
  exact ⟨hxW, hxs⟩

theorem mem_interior_image_components_preimage
    {M : Type*} [TopologicalSpace M] {s : Set M} [LocallyConnectedSpace s]
    (R : Set (ConnectedComponents s)) {x : s}
    (hx : ConnectedComponents.mk x ∈ R) (hxs : x.val ∈ interior s) :
    x.val ∈ interior ((Subtype.val : s → M) '' (ConnectedComponents.mk ⁻¹' R)) := by
  apply mem_interior_image_val_of_isOpen _ hx hxs
  exact (isOpen_discrete R).preimage ConnectedComponents.continuous_coe

end DifferentialGeometry.Topology
