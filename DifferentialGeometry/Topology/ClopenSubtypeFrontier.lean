import Mathlib.Topology.Constructions

/-!
# ClopenSubtypeFrontier
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Topology

theorem frontier_subtype_image_subset_of_isClopen
    {X : Type*} [TopologicalSpace X] {K : Set X} {A : Set K}
    (hK : IsClosed K) (hA : IsClopen A) :
    frontier (Subtype.val '' A) ⊆ frontier K ∩ (Subtype.val '' A) := by
  have hclosed : IsClosed (Subtype.val '' A) :=
    hK.isClosedMap_subtype_val A hA.1
  intro x hx
  have hxA : x ∈ Subtype.val '' A := hclosed.closure_eq ▸ hx.1
  have hxK : x ∈ K := by
    obtain ⟨a, _, rfl⟩ := hxA
    exact a.property
  refine ⟨⟨subset_closure hxK, ?_⟩, hxA⟩
  intro hi
  obtain ⟨U, hU, hAU⟩ := hA.2.image_val
  have hxU : x ∈ U := ((congrArg (x ∈ ·) hAU).mp hxA).1
  have hsub : U ∩ interior K ⊆ Subtype.val '' A := by
    rw [hAU]
    exact inter_subset_inter_right U interior_subset
  exact hx.2 (interior_maximal hsub (hU.inter isOpen_interior) ⟨hxU, hi⟩)

end DifferentialGeometry.Topology
