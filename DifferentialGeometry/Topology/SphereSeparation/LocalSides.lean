import DifferentialGeometry.Topology.SphereSeparation.Sides

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open Set

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S U V O : Set X}

theorem neighborhood_halves_opposite (d : SphereSides S)
    (hS : S.Nonempty) (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ Sᶜ) (hVS : V ⊆ Sᶜ)
    (hOopen : IsOpen O) (hSO : S ⊆ O) (hO : O ⊆ (U ∪ S) ∪ V) :
    Xor (U ⊆ d.compactSide ∧ V ⊆ d.endSide)
      (U ⊆ d.endSide ∧ V ⊆ d.compactSide) := by
  have not_both_compact :
      ¬ (U ⊆ d.compactSide ∧ V ⊆ d.compactSide) := by
    rintro ⟨hUB, hVB⟩
    obtain ⟨s, hsS⟩ := hS
    have hsClosure : s ∈ closure d.endSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_endSide] using hsS
    obtain ⟨x, hxO, hxE⟩ := mem_closure_iff.1 hsClosure O hOopen (hSO hsS)
    rcases hO hxO with (hxU | hxS) | hxV
    · exact Set.disjoint_left.1 d.disjoint (hUB hxU) hxE
    · exact Set.disjoint_left.1 d.endSide_disjoint_sphere hxE hxS
    · exact Set.disjoint_left.1 d.disjoint (hVB hxV) hxE
  have not_both_end : ¬ (U ⊆ d.endSide ∧ V ⊆ d.endSide) := by
    rintro ⟨hUE, hVE⟩
    obtain ⟨s, hsS⟩ := hS
    have hsClosure : s ∈ closure d.compactSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_compactSide] using hsS
    obtain ⟨x, hxO, hxB⟩ := mem_closure_iff.1 hsClosure O hOopen (hSO hsS)
    rcases hO hxO with (hxU | hxS) | hxV
    · exact Set.disjoint_left.1 d.disjoint hxB (hUE hxU)
    · exact Set.disjoint_left.1 d.compactSide_disjoint_sphere hxB hxS
    · exact Set.disjoint_left.1 d.disjoint hxB (hVE hxV)
  rcases d.subset_compactSide_or_subset_endSide hU.isPreconnected hUS with hUB | hUE
  · rcases d.subset_compactSide_or_subset_endSide hV.isPreconnected hVS with hVB | hVE
    · exact False.elim (not_both_compact ⟨hUB, hVB⟩)
    · refine Or.inl ⟨⟨hUB, hVE⟩, ?_⟩
      rintro ⟨hUE', _⟩
      obtain ⟨x, hxU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB hxU) (hUE' hxU)
  · rcases d.subset_compactSide_or_subset_endSide hV.isPreconnected hVS with hVB | hVE
    · refine Or.inr ⟨⟨hUE, hVB⟩, ?_⟩
      rintro ⟨hUB', _⟩
      obtain ⟨x, hxU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB' hxU) (hUE hxU)
    · exact False.elim (not_both_end ⟨hUE, hVE⟩)

end SphereSides

end DifferentialGeometry.Topology.SphereSeparation
