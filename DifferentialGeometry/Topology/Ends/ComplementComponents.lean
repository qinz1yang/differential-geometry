import DifferentialGeometry.Topology.Ends.FiniteEnds

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Topology

private theorem connectedComponentIn_eq_of_open_partition
    {X : Type*} [TopologicalSpace X] {S B E : Set X}
    (hB : IsConnected B) (hBopen : IsOpen B) (hEopen : IsOpen E)
    (hdisjoint : Disjoint B E) (hunion : B ∪ E = Sᶜ)
    {b : X} (hb : b ∈ B) : connectedComponentIn Sᶜ b = B := by
  have hBsub : B ⊆ Sᶜ := by
    rw [← hunion]
    exact subset_union_left
  apply Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hBopen hEopen hdisjoint
    · rw [hunion]
      exact connectedComponentIn_subset Sᶜ b
    · exact ⟨b, mem_connectedComponentIn (hBsub hb), hb⟩
  · exact hB.isPreconnected.subset_connectedComponentIn hb hBsub

theorem exactly_one_compact_closure_of_not_hasAtLeastEnds_two
    {X : Type*} [TopologicalSpace X] [NoncompactSpace X]
    (hends : ¬ HasAtLeastEnds X 2)
    {S B E : Set X} (hS : IsCompact S)
    (hB : IsConnected B) (hE : IsConnected E)
    (hBopen : IsOpen B) (hEopen : IsOpen E)
    (hdisjoint : Disjoint B E) (hunion : B ∪ E = Sᶜ) :
    (IsCompact (closure B) ∧ ¬ IsCompact (closure E)) ∨
      (IsCompact (closure E) ∧ ¬ IsCompact (closure B)) := by
  classical
  obtain ⟨b, hb⟩ := hB.nonempty
  obtain ⟨e, he⟩ := hE.nonempty
  have hbavoid : b ∉ S := by
    have hmem : b ∈ B ∪ E := Or.inl hb
    rwa [hunion] at hmem
  have heavoid : e ∉ S := by
    have hmem : e ∈ B ∪ E := Or.inr he
    rwa [hunion] at hmem
  have hcompB : connectedComponentIn Sᶜ b = B :=
    connectedComponentIn_eq_of_open_partition hB hBopen hEopen hdisjoint hunion hb
  have hcompE : connectedComponentIn Sᶜ e = E :=
    connectedComponentIn_eq_of_open_partition hE hEopen hBopen hdisjoint.symm
      ((union_comm E B).trans hunion) he
  have hne : B ≠ E := by
    intro heq
    exact Set.disjoint_left.mp hdisjoint hb (heq ▸ hb)
  have hsome : IsCompact (closure B) ∨ IsCompact (closure E) := by
    by_contra hnone
    have hBn : ¬ IsCompact (closure B) := fun h => hnone (Or.inl h)
    have hEn : ¬ IsCompact (closure E) := fun h => hnone (Or.inr h)
    apply hends
    let x : Fin 2 → X := fun i => if i = 0 then b else e
    have hcomponents (i : Fin 2) : connectedComponentIn Sᶜ (x i) =
        if i = 0 then B else E := by
      by_cases hi : i = 0
      · simpa only [x, hi, ite_true] using hcompB
      · simpa only [x, hi, ite_false] using hcompE
    refine ⟨S, hS, x, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · simpa only [x, hi, ite_true] using hbavoid
      · simpa only [x, hi, ite_false] using heavoid
    · intro i j hij
      change connectedComponentIn Sᶜ (x i) = connectedComponentIn Sᶜ (x j) at hij
      rw [hcomponents i, hcomponents j] at hij
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · exact hi.trans hj.symm
        · rw [if_pos hi, if_neg hj] at hij
          exact False.elim (hne hij)
      · by_cases hj : j = 0
        · rw [if_neg hi, if_pos hj] at hij
          exact False.elim (hne hij.symm)
        · exact (Fin.eq_one_of_ne_zero i hi).trans (Fin.eq_one_of_ne_zero j hj).symm
    · intro i
      rw [hcomponents i]
      by_cases hi : i = 0
      · rw [if_pos hi]
        exact hBn
      · rw [if_neg hi]
        exact hEn
  have hnotboth : ¬ (IsCompact (closure B) ∧ IsCompact (closure E)) := by
    rintro ⟨hBc, hEc⟩
    have hcover : closure B ∪ closure E ∪ S = univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hxS : x ∈ S
      · exact Or.inr hxS
      · have hxBE : x ∈ B ∪ E := by rw [hunion]; exact hxS
        rcases hxBE with hxB | hxE
        · exact Or.inl (Or.inl (subset_closure hxB))
        · exact Or.inl (Or.inr (subset_closure hxE))
    exact noncompact_univ X (hcover ▸ (hBc.union hEc).union hS)
  rcases hsome with hBc | hEc
  · exact Or.inl ⟨hBc, fun hEc => hnotboth ⟨hBc, hEc⟩⟩
  · exact Or.inr ⟨hEc, fun hBc => hnotboth ⟨hBc, hEc⟩⟩

end DifferentialGeometry.Geometry.Topology
