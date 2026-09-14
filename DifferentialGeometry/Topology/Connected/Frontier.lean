import Mathlib.Topology.Connected.Basic
import DifferentialGeometry.Topology.Frontier

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

theorem frontier_union_eq_iUnion_of_isPreconnected
    {X ι : Type*} [TopologicalSpace X] {A B : Set X} (F : ι → Set X)
    (hF : ∀ i, IsPreconnected (F i)) (hfront : frontier A = ⋃ i, F i)
    (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = ⋃ i ∈ {i | Disjoint (F i) (closure B)}, F i := by
  rw [frontier_union_eq_sdiff_closure_of_frontier_subset_interior hB]
  have hsub (i : ι) : F i ⊆ frontier A := by
    rw [hfront]
    exact subset_iUnion F i
  have havoid (i : ι) : Disjoint (F i) (frontier B) :=
    Set.disjoint_left.mpr (fun x hxi hxB ↦ (hsub i hxi).2 (hB hxB))
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hfront ▸ hxA)
    have hdisjoint : Disjoint (F i) (closure B) := by
      apply Set.disjoint_left.mpr
      intro y hyi hyB
      have hyint : y ∈ interior B := by
        by_contra hy
        exact Set.disjoint_left.mp (havoid i) hyi ⟨hyB, hy⟩
      have hin := subset_interior_of_isPreconnected_of_disjoint_frontier
        (hF i) (havoid i) ⟨y, hyi, hyint⟩
      exact hxB (interior_subset_closure (hin hxi))
    exact mem_iUnion₂.mpr ⟨i, hdisjoint, hxi⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact ⟨hsub i hxi, fun hxB ↦ Set.disjoint_left.mp hi hxi hxB⟩

theorem frontier_union_eq_iUnion_of_isClosed_of_isPreconnected
    {X ι : Type*} [TopologicalSpace X] {A B : Set X} (F : ι → Set X)
    (hF : ∀ i, IsPreconnected (F i)) (hfront : frontier A = ⋃ i, F i)
    (hclosed : IsClosed B) (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = ⋃ i ∈ {i | Disjoint (F i) B}, F i := by
  rw [frontier_union_eq_iUnion_of_isPreconnected F hF hfront hB, hclosed.closure_eq]

end DifferentialGeometry.Topology
