import Mathlib.Topology.Connected.Clopen
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

theorem eq_of_closure_interior_eq_of_disjoint_interior_frontier
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (interior A) = A) (hB : closure (interior B) = B)
    (hcA : IsPreconnected (interior A)) (hcB : IsPreconnected (interior B))
    (hdAB : Disjoint (interior A) (frontier B))
    (hdBA : Disjoint (interior B) (frontier A))
    (hmeet : (interior A ∩ interior B).Nonempty) : A = B := by
  have hAB := subset_interior_of_isPreconnected_of_disjoint_frontier hcA hdAB hmeet
  have hBA := subset_interior_of_isPreconnected_of_disjoint_frontier hcB hdBA
    (inter_comm (interior A) (interior B) ▸ hmeet)
  rw [← hA, ← hB, subset_antisymm hAB hBA]

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

variable {X : Type*} [TopologicalSpace X]

theorem isClopen_preimage_of_frontier_union_subset
    {K W C S : Set X} (hK : IsClosed K) (hS : IsClosed S)
    (hKS : Disjoint K S) (hfront : frontier (W ∪ K) ⊆ S)
    (hcore : W ∩ C ⊆ K ∪ S) :
    IsClopen ((Subtype.val : C → X) ⁻¹' K) := by
  refine ⟨hK.preimage continuous_subtype_val, ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxnot : x.val ∉ S := disjoint_left.mp hKS hx
  have hxfront : x.val ∉ frontier (W ∪ K) := fun h => hxnot (hfront h)
  have hxint : x.val ∈ interior (W ∪ K) :=
    (mem_interior_iff_notMem_frontier (show x.val ∈ W ∪ K from Or.inr hx)).mpr hxfront
  have hU : IsOpen (interior (W ∪ K) \ S) := isOpen_interior.sdiff hS
  apply Filter.mem_of_superset
    ((hU.preimage continuous_subtype_val).mem_nhds (show x.val ∈ interior (W ∪ K) \ S from
      ⟨hxint,hxnot⟩))
  intro y hy
  rcases interior_subset hy.1 with hyW | hyK
  · exact (hcore ⟨hyW,y.property⟩).resolve_right hy.2
  · exact hyK

theorem connectedComponent_eq_preimage_of_frontier_union_subset
    {K W C S : Set X} (hK : IsClosed K) (hconn : IsPreconnected K)
    (hKC : K ⊆ C) (hS : IsClosed S) (hKS : Disjoint K S)
    (hfront : frontier (W ∪ K) ⊆ S) (hcore : W ∩ C ⊆ K ∪ S)
    (x : C) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : C → X) ⁻¹' K := by
  have hcl := isClopen_preimage_of_frontier_union_subset hK hS hKS hfront hcore
  have hpre : IsPreconnected ((Subtype.val : C → X) ⁻¹' K) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hKC]
  exact Subset.antisymm (hcl.connectedComponent_subset hx) (hpre.subset_connectedComponent hx)


end DifferentialGeometry.Topology
