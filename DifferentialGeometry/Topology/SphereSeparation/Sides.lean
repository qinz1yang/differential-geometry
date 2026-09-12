import DifferentialGeometry.Topology.SphereSeparation.Defs

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open Set

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

theorem subset_endSide_of_not_isCompact_closure (d : SphereSides S)
    (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ)
    (hCnc : ¬ IsCompact (closure C)) :
    C ⊆ d.endSide := by
  rcases d.subset_compactSide_or_subset_endSide hC hCS with hCB | hCE
  · exfalso
    apply hCnc
    exact d.isCompact_closure_compactSide.of_isClosed_subset isClosed_closure
      (closure_mono hCB)
  · exact hCE

theorem eq_compactSide_or_eq_endSide_of_isOpen_of_closure_subset
    (d : SphereSides S) (hCopen : IsOpen C) (hCconn : IsConnected C)
    (hCcompl : C ⊆ Sᶜ) (hclosure : closure C ⊆ C ∪ S) :
    C = d.compactSide ∨ C = d.endSide := by
  have hside : C ⊆ d.compactSide ∨ C ⊆ d.endSide :=
    d.subset_compactSide_or_subset_endSide hCconn.isPreconnected hCcompl
  rcases hside with hCB | hCE
  · apply Or.inl
    apply Set.Subset.antisymm hCB
    have hcover : d.compactSide ⊆ C ∪ (closure C)ᶜ := by
      intro x hxB
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · refine Or.inr ?_
        intro hxCl
        rcases hclosure hxCl with hxC' | hxS
        · exact hxC hxC'
        · exact d.compactSide_disjoint_sphere.le_bot ⟨hxB, hxS⟩
    have hinter : (d.compactSide ∩ C).Nonempty := by
      obtain ⟨x, hxC⟩ := hCconn.nonempty
      exact ⟨x, hCB hxC, hxC⟩
    exact d.isConnected_compactSide.isPreconnected.subset_left_of_subset_union
      hCopen isClosed_closure.isOpen_compl
      (by
        rw [Set.disjoint_left]
        intro x hxC hxCl
        exact hxCl (subset_closure hxC))
      hcover hinter
  · apply Or.inr
    apply Set.Subset.antisymm hCE
    have hcover : d.endSide ⊆ C ∪ (closure C)ᶜ := by
      intro x hxE
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · refine Or.inr ?_
        intro hxCl
        rcases hclosure hxCl with hxC' | hxS
        · exact hxC hxC'
        · exact d.endSide_disjoint_sphere.le_bot ⟨hxE, hxS⟩
    have hinter : (d.endSide ∩ C).Nonempty := by
      obtain ⟨x, hxC⟩ := hCconn.nonempty
      exact ⟨x, hCE hxC, hxC⟩
    exact d.isConnected_endSide.isPreconnected.subset_left_of_subset_union
      hCopen isClosed_closure.isOpen_compl
      (by
        rw [Set.disjoint_left]
        intro x hxC hxCl
        exact hxCl (subset_closure hxC))
      hcover hinter

theorem compactSide_inter_compactSide_nonempty (d₁ d₂ : SphereSides S) :
    (d₁.compactSide ∩ d₂.compactSide).Nonempty := by
  by_contra hne
  have hB₁E₂ : d₁.compactSide ⊆ d₂.endSide := by
    rcases d₂.subset_compactSide_or_subset_endSide
        d₁.isConnected_compactSide.isPreconnected d₁.compactSide_subset_compl with hB₁B₂ | hB₁E₂
    · obtain ⟨x, hx⟩ := d₁.compactSide_nonempty
      exact False.elim (hne ⟨x, hx, hB₁B₂ hx⟩)
    · exact hB₁E₂
  have hE₂B₁ : d₂.endSide ⊆ d₁.compactSide := by
    apply d₁.subset_compactSide_of_isPreconnected_of_inter_nonempty
      d₂.isConnected_endSide.isPreconnected d₂.endSide_subset_compl
    obtain ⟨x, hx⟩ := d₁.compactSide_nonempty
    exact ⟨x, hB₁E₂ hx, hx⟩
  have hEq : d₁.compactSide = d₂.endSide :=
    Set.Subset.antisymm hB₁E₂ hE₂B₁
  apply d₂.not_isCompact_closure_endSide
  rw [← hEq]
  exact d₁.isCompact_closure_compactSide

theorem side_sets_unique (d₁ d₂ : SphereSides S) :
    d₁.compactSide = d₂.compactSide ∧ d₁.endSide = d₂.endSide := by
  have hBB : d₁.compactSide = d₂.compactSide := by
    apply Set.Subset.antisymm
    · apply d₂.subset_compactSide_of_isPreconnected_of_inter_nonempty
        d₁.isConnected_compactSide.isPreconnected d₁.compactSide_subset_compl
      exact compactSide_inter_compactSide_nonempty d₁ d₂
    · apply d₁.subset_compactSide_of_isPreconnected_of_inter_nonempty
        d₂.isConnected_compactSide.isPreconnected d₂.compactSide_subset_compl
      obtain ⟨x, hx₁, hx₂⟩ := compactSide_inter_compactSide_nonempty d₁ d₂
      exact ⟨x, hx₂, hx₁⟩
  refine ⟨hBB, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxE₁
    have hx : x ∈ d₂.compactSide ∪ d₂.endSide := by
      rw [d₂.union_eq_compl]
      exact d₁.endSide_subset_compl hxE₁
    rcases hx with hxB₂ | hxE₂
    · have hxB₁ : x ∈ d₁.compactSide := by simpa only [hBB] using hxB₂
      exact False.elim (Set.disjoint_left.1 d₁.disjoint hxB₁ hxE₁)
    · exact hxE₂
  · intro x hxE₂
    have hx : x ∈ d₁.compactSide ∪ d₁.endSide := by
      rw [d₁.union_eq_compl]
      exact d₂.endSide_subset_compl hxE₂
    rcases hx with hxB₁ | hxE₁
    · have hxB₂ : x ∈ d₂.compactSide := by simpa only [← hBB] using hxB₁
      exact False.elim (Set.disjoint_left.1 d₂.disjoint hxB₂ hxE₂)
    · exact hxE₁

theorem side_sets_unique_of_core_properties
    (d : SphereSides S) (B E : Set X)
    (hBopen : IsOpen B) (hEopen : IsOpen E)
    (hBconnected : IsConnected B) (_hEconnected : IsConnected E)
    (hdisjoint : Disjoint B E) (hunion : B ∪ E = Sᶜ)
    (hBcompact : IsCompact (closure B))
    (_hEnoncompact : ¬ IsCompact (closure E)) :
    B = d.compactSide ∧ E = d.endSide := by
  have hBcompl : B ⊆ Sᶜ := by
    intro x hx
    rw [← hunion]
    exact Or.inl hx
  have hBside : B ⊆ d.compactSide ∨ B ⊆ d.endSide :=
    d.subset_compactSide_or_subset_endSide hBconnected.isPreconnected hBcompl
  have hBeq : B = d.compactSide := by
    rcases hBside with hBcompactSide | hBendSide
    · apply Set.Subset.antisymm hBcompactSide
      apply d.isConnected_compactSide.isPreconnected.subset_left_of_subset_union
        hBopen hEopen hdisjoint
      · simpa only [hunion] using d.compactSide_subset_compl
      · obtain ⟨x, hxB⟩ := hBconnected.nonempty
        exact ⟨x, hBcompactSide hxB, hxB⟩
    · have hEndSubsetB : d.endSide ⊆ B := by
        apply d.isConnected_endSide.isPreconnected.subset_left_of_subset_union
          hBopen hEopen hdisjoint
        · simpa only [hunion] using d.endSide_subset_compl
        · obtain ⟨x, hxB⟩ := hBconnected.nonempty
          exact ⟨x, hBendSide hxB, hxB⟩
      have hEqEnd : B = d.endSide :=
        Set.Subset.antisymm hBendSide hEndSubsetB
      exfalso
      apply d.not_isCompact_closure_endSide
      rw [← hEqEnd]
      exact hBcompact
  refine ⟨hBeq, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxE
    have hxCompl : x ∈ Sᶜ := by
      rw [← hunion]
      exact Or.inr hxE
    rw [d.compl_eq_union] at hxCompl
    rcases hxCompl with hxCompact | hxEnd
    · exact False.elim
        (Set.disjoint_left.1 hdisjoint (hBeq.symm ▸ hxCompact) hxE)
    · exact hxEnd
  · intro x hxEnd
    have hxCandidate : x ∈ B ∪ E := by
      rw [hunion]
      exact d.endSide_subset_compl hxEnd
    rcases hxCandidate with hxB | hxE
    · exact False.elim
        (Set.disjoint_left.1 d.disjoint (hBeq ▸ hxB) hxEnd)
    · exact hxE

theorem unique (d₁ d₂ : SphereSides S) : d₁ = d₂ := by
  rcases side_sets_unique d₁ d₂ with ⟨hB, hE⟩
  cases d₁
  cases d₂
  simp_all

instance : Subsingleton (SphereSides S) :=
  ⟨unique⟩

theorem not_isPreconnected_compl (d : SphereSides S) : ¬ IsPreconnected Sᶜ := by
  intro hpre
  rcases d.subset_compactSide_or_subset_endSide hpre subset_rfl with h | h
  · have hsub : d.endSide ⊆ ∅ := fun x hx =>
      Set.disjoint_left.mp d.disjoint (h (d.endSide_subset_compl hx)) hx
    obtain ⟨x, hx⟩ := d.endSide_nonempty
    rw [Set.subset_empty_iff.mp hsub] at hx
    exact hx
  · have hsub : d.compactSide ⊆ ∅ := fun x hx =>
      Set.disjoint_left.mp d.disjoint hx (h (d.compactSide_subset_compl hx))
    obtain ⟨x, hx⟩ := d.compactSide_nonempty
    rw [Set.subset_empty_iff.mp hsub] at hx
    exact hx

end SphereSides

end DifferentialGeometry.Topology.SphereSeparation
