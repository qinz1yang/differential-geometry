import Mathlib.Topology.Connected.Basic

namespace Poincare.Topology

open Set

theorem subset_interior_of_isPreconnected_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsPreconnected A) (hdisj : Disjoint A (frontier B))
    (hmeet : (A ∩ interior B).Nonempty) : A ⊆ interior B := by
  apply hA.subset_of_closure_inter_subset isOpen_interior hmeet
  intro x hx
  by_contra hxi
  exact (Set.disjoint_left.mp hdisj hx.2)
    ⟨closure_mono interior_subset hx.1, hxi⟩

theorem eq_of_frontier_eq_of_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (interior A) = A) (hB : closure (interior B) = B)
    (hcA : IsPreconnected (interior A)) (hcB : IsPreconnected (interior B))
    (hfrontier : frontier A = frontier B)
    (hmeet : (interior A ∩ interior B).Nonempty) : A = B := by
  have hAB : interior A ⊆ interior B :=
    subset_interior_of_isPreconnected_of_disjoint_frontier hcA
      (hfrontier ▸ disjoint_interior_frontier) hmeet
  have hBA : interior B ⊆ interior A :=
    subset_interior_of_isPreconnected_of_disjoint_frontier hcB
      (hfrontier.symm ▸ disjoint_interior_frontier)
      (inter_comm (interior A) (interior B) ▸ hmeet)
  rw [← hA, ← hB, subset_antisymm hAB hBA]

end Poincare.Topology
