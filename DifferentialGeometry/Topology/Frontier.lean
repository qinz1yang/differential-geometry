import Mathlib.Topology.Closure

namespace DifferentialGeometry.Topology

open Set

theorem frontier_union_eq_sdiff_closure_of_frontier_subset_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = frontier A \ closure B := by
  apply Subset.antisymm
  · intro x hx
    have hxA : x ∈ frontier A := by
      rcases frontier_union_subset A B hx with hA | hB'
      · exact hA.1
      · exact False.elim (hx.2 (interior_mono subset_union_left (hB hB'.2)))
    refine ⟨hxA, ?_⟩
    intro hxB
    apply hxA.2 (hB ⟨hxB, ?_⟩)
    intro hxBi
    exact hx.2 (interior_mono subset_union_right hxBi)
  · rintro x ⟨hxA, hxB⟩
    refine ⟨closure_mono subset_union_left hxA.1, ?_⟩
    intro hx
    apply hxA.2
    apply mem_interior.mpr
    refine ⟨interior (A ∪ B) ∩ (closure B)ᶜ, ?_,
      isOpen_interior.inter isClosed_closure.isOpen_compl, hx, hxB⟩
    intro y hy
    exact (interior_subset hy.1).resolve_right (fun h ↦ hy.2 (subset_closure h))

theorem frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hclosed : IsClosed B) (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = frontier A \ B := by
  rw [frontier_union_eq_sdiff_closure_of_frontier_subset_interior hB, hclosed.closure_eq]

end DifferentialGeometry.Topology
