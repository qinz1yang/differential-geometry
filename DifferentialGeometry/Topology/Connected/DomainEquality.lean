import Mathlib.Topology.Connected.Basic

open Set

namespace Poincare.Topology

theorem eq_of_regularClosed_subset_of_frontier_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (interior A) = A) (hB : closure (interior B) = B)
    (hconn : IsPreconnected (interior B)) (hne : A.Nonempty)
    (hsub : A ⊆ B) (hd : Disjoint (frontier A) (interior B)) : A = B := by
  have hi : (interior A).Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty, closure_empty] at hA
    exact hne.ne_empty hA.symm
  have hinc : interior A ⊆ interior B := interior_mono hsub
  have hreverse : interior B ⊆ interior A := by
    apply hconn.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨x, hx⟩ := hi
      exact ⟨x, hinc hx, hx⟩
    · rintro x ⟨hx, hxB⟩
      rw [hA] at hx
      apply (mem_interior_iff_notMem_frontier hx).mpr
      exact fun hf ↦ hd.le_bot ⟨hf, hxB⟩
  rw [← hA, ← hB, Set.Subset.antisymm hinc hreverse]

end Poincare.Topology
