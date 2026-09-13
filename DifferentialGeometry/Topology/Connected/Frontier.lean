import Mathlib.Topology.Connected.Basic

namespace DifferentialGeometry.Topology

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

theorem inter_union_frontier_nonempty_of_subset_union_interior
    {X : Type*} [TopologicalSpace X] {P S T U : Set X}
    (hP : IsPreconnected P) (hout : (P \ U).Nonempty)
    (hmeet : (P ∩ S).Nonempty) (hS : S ⊆ T ∪ interior U) :
    (P ∩ (T ∪ frontier U)).Nonempty := by
  obtain ⟨x, hxP, hxS⟩ := hmeet
  rcases hS hxS with hxT | hxU
  · exact ⟨x, hxP, Or.inl hxT⟩
  · by_contra h
    have hdisj : Disjoint P (frontier U) := Set.disjoint_left.mpr
      (fun y hyP hyU => h ⟨y, hyP, Or.inr hyU⟩)
    have hsub := subset_interior_of_isPreconnected_of_disjoint_frontier hP hdisj
      ⟨x, hxP, hxU⟩
    obtain ⟨y, hyP, hyU⟩ := hout
    exact hyU (interior_subset (hsub hyP))

end DifferentialGeometry.Topology
