import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

namespace DifferentialGeometry.Topology

open Set

theorem isPreconnected_of_locallyFinite_closed_attachments_with_preconnected_hulls
    {M ι : Type*} [TopologicalSpace M]
    {K : Set M} (E : ι → Set M) (hK : IsClosed K)
    (hlocal : LocallyFinite E) (hclosed : ∀ i, IsClosed (E i))
    (hoverlap : ∀ i j, i ≠ j → E i ∩ E j ⊆ K)
    (hattach : ∀ i, ∃ L, IsPreconnected L ∧ K ∩ E i ⊆ L ∧ L ⊆ K)
    (hunion : IsPreconnected (K ∪ ⋃ i, E i)) : IsPreconnected K := by
  classical
  refine isPreconnected_iff_subset_of_disjoint_closed.mpr ?_
  intro A B hA hB hcover hdisjoint
  have hnot {x : M} (hxK : x ∈ K) (hxA : x ∈ A) (hxB : x ∈ B) : False := by
    have hx : x ∈ K ∩ (A ∩ B) := ⟨hxK, hxA, hxB⟩
    rw [hdisjoint] at hx
    exact hx
  let chosen : Set ι := {i | (K ∩ E i ∩ A).Nonempty}
  have hchosen : ∀ i ∈ chosen, K ∩ E i ⊆ A := by
    intro i hi
    obtain ⟨L, hL, hcontact, hLK⟩ := hattach i
    have hcov : L ⊆ A ∪ B := fun _ hx => hcover (hLK hx)
    have hd : L ∩ (A ∩ B) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hnot (hLK hx.1) hx.2.1 hx.2.2
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hL
      A B hA hB hcov hd with h | h
    · exact hcontact.trans h
    · obtain ⟨x, hx, hxA⟩ := hi
      exact False.elim (hnot hx.1 hxA (h (hcontact hx)))
  have hunchosen : ∀ i ∉ chosen, K ∩ E i ⊆ B := by
    intro i hi x hx
    rcases hcover hx.1 with hxA | hxB
    · exact False.elim (hi ⟨x, hx, hxA⟩)
    · exact hxB
  let U : Set M := (K ∩ A) ∪ ⋃ i : chosen, E i.val
  let V : Set M := (K ∩ B) ∪ ⋃ i : {i : ι // i ∉ chosen}, E i.val
  have hU : IsClosed U := (hK.inter hA).union
    ((hlocal.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hclosed i.val)
  have hV : IsClosed V := (hK.inter hB).union
    ((hlocal.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hclosed i.val)
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    intro x hxU hxV
    rcases hxU with hxA | hxE
    · rcases hxV with hxB | hxF
      · exact hnot hxA.1 hxA.2 hxB.2
      · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxF
        exact hnot hxA.1 hxA.2 (hunchosen j.val j.property ⟨hxA.1, hxj⟩)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
      rcases hxV with hxB | hxF
      · exact hnot hxB.1 (hchosen i.val i.property ⟨hxB.1, hxi⟩) hxB.2
      · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxF
        have hij : i.val ≠ j.val := by
          intro heq
          exact j.property (heq ▸ i.property)
        have hxK := hoverlap i.val j.val hij ⟨hxi, hxj⟩
        exact hnot hxK (hchosen i.val i.property ⟨hxK, hxi⟩)
          (hunchosen j.val j.property ⟨hxK, hxj⟩)
  have htotal : K ∪ ⋃ i, E i ⊆ U ∪ V := by
    intro x hx
    rcases hx with hxK | hxE
    · rcases hcover hxK with hxA | hxB
      · exact Or.inl (Or.inl ⟨hxK, hxA⟩)
      · exact Or.inr (Or.inl ⟨hxK, hxB⟩)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
      by_cases hi : i ∈ chosen
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩))
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hunion U V hU hV htotal
    (by rw [hUV.inter_eq, inter_empty]) with h | h
  · left
    intro x hxK
    rcases h (Or.inl hxK) with hxA | hxE
    · exact hxA.2
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
      exact hchosen i.val i.property ⟨hxK, hxi⟩
  · right
    intro x hxK
    rcases h (Or.inl hxK) with hxB | hxE
    · exact hxB.2
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
      exact hunchosen i.val i.property ⟨hxK, hxi⟩

theorem isPreconnected_of_finite_closed_attachments_with_preconnected_hulls
    {M ι : Type*} [TopologicalSpace M] [Finite ι]
    {K : Set M} (E : ι → Set M) (hK : IsClosed K)
    (hclosed : ∀ i, IsClosed (E i))
    (hoverlap : ∀ i j, i ≠ j → E i ∩ E j ⊆ K)
    (hattach : ∀ i, ∃ L, IsPreconnected L ∧ K ∩ E i ⊆ L ∧ L ⊆ K)
    (hunion : IsPreconnected (K ∪ ⋃ i, E i)) : IsPreconnected K :=
  isPreconnected_of_locallyFinite_closed_attachments_with_preconnected_hulls E hK
    (locallyFinite_of_finite E) hclosed hoverlap hattach hunion

theorem isPreconnected_of_locallyFinite_closed_attachments
    {M ι : Type*} [TopologicalSpace M]
    {K : Set M} (E : ι → Set M) (hK : IsClosed K)
    (hlocal : LocallyFinite E) (hclosed : ∀ i, IsClosed (E i))
    (hoverlap : ∀ i j, i ≠ j → E i ∩ E j ⊆ K)
    (hattach : ∀ i, IsPreconnected (K ∩ E i))
    (hunion : IsPreconnected (K ∪ ⋃ i, E i)) : IsPreconnected K :=
  isPreconnected_of_locallyFinite_closed_attachments_with_preconnected_hulls E hK hlocal
    hclosed hoverlap (fun i => ⟨K ∩ E i, hattach i, Subset.rfl, inter_subset_left⟩) hunion

theorem isPreconnected_of_finite_closed_attachments
    {M ι : Type*} [TopologicalSpace M] [Finite ι]
    {K : Set M} (E : ι → Set M) (hK : IsClosed K)
    (hclosed : ∀ i, IsClosed (E i))
    (hoverlap : ∀ i j, i ≠ j → E i ∩ E j ⊆ K)
    (hattach : ∀ i, IsPreconnected (K ∩ E i))
    (hunion : IsPreconnected (K ∪ ⋃ i, E i)) : IsPreconnected K :=
  isPreconnected_of_locallyFinite_closed_attachments E hK (locallyFinite_of_finite E)
    hclosed hoverlap hattach hunion

end DifferentialGeometry.Topology
