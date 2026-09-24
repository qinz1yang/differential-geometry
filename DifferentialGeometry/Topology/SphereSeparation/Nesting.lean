import DifferentialGeometry.Topology.SphereSeparation.Sides

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open Set

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S₁ S₂ : Set X}

private theorem frontier_subset_closure' (A : Set X) : frontier A ⊆ closure A :=
  frontier_subset_closure

theorem compactSide_disjoint_or_subset_of_isPreconnected_sdiff
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hconn : IsPreconnected (S₂ \ S₁)) :
    Disjoint d₁.compactSide d₂.compactSide ∨
      d₁.compactSide ⊆ d₂.compactSide ∨ d₂.compactSide ⊆ d₁.compactSide := by
  rcases d₁.subset_compactSide_or_subset_endSide hconn (sdiff_subset_compl S₂ S₁) with hS | hS
  · have havoid : d₁.endSide ⊆ S₂ᶜ := by
      intro x hx hxS
      exact d₁.disjoint.le_bot ⟨hS ⟨hxS, d₁.endSide_subset_compl hx⟩, hx⟩
    have hend : d₁.endSide ⊆ d₂.endSide :=
      d₂.subset_endSide_of_not_isCompact_closure d₁.isConnected_endSide.isPreconnected
        havoid d₁.not_isCompact_closure_endSide
    have hsub : d₂.compactSide ⊆ closure d₁.compactSide := by
      intro x hx
      rw [d₁.closure_compactSide]
      by_cases hxS : x ∈ S₁
      · exact Or.inr hxS
      · have hparts : x ∈ d₁.compactSide ∪ d₁.endSide := d₁.compl_eq_union ▸ hxS
        exact Or.inl (hparts.resolve_right (fun he => d₂.disjoint.le_bot ⟨hx, hend he⟩))
    right
    right
    simpa only [d₂.isOpen_compactSide.interior_eq, d₁.interior_closure_compactSide] using
      interior_mono hsub
  · have havoid : d₁.compactSide ⊆ S₂ᶜ := by
      intro x hx hxS
      exact d₁.disjoint.le_bot ⟨hx, hS ⟨hxS, d₁.compactSide_subset_compl hx⟩⟩
    rcases d₂.subset_compactSide_or_subset_endSide
      d₁.isConnected_compactSide.isPreconnected havoid with hsub | hsub
    · exact Or.inr (Or.inl hsub)
    · exact Or.inl (Set.disjoint_left.mpr fun _ hx hy => d₂.disjoint.le_bot ⟨hy, hsub hx⟩)

theorem closure_compactSide_inter_eq_of_disjoint
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hd : Disjoint d₁.compactSide d₂.compactSide) :
    closure d₁.compactSide ∩ closure d₂.compactSide = S₁ ∩ S₂ := by
  have hd₁ := hd.closure_left d₂.isOpen_compactSide
  have hd₂ := hd.closure_right d₁.isOpen_compactSide
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · have := d₁.closure_compactSide ▸ hx
      exact this.resolve_left (fun h => hd₂.le_bot ⟨h, hy⟩)
    · have := d₂.closure_compactSide ▸ hy
      exact this.resolve_left (fun h => hd₁.le_bot ⟨hx, h⟩)
  · rintro ⟨hx, hy⟩
    exact ⟨d₁.closure_compactSide ▸ Or.inr hx, d₂.closure_compactSide ▸ Or.inr hy⟩

theorem disjoint_sides_nested
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hS₁S₂ : Disjoint S₁ S₂) (hS₂conn : IsConnected S₂)
    (hBB : (d₁.compactSide ∩ d₂.compactSide).Nonempty) :
    Xor (closure d₁.compactSide ⊆ d₂.compactSide)
      (closure d₂.compactSide ⊆ d₁.compactSide) := by
  have hS₂S₁ : S₂ ⊆ S₁ᶜ := by
    intro x hxS₂ hxS₁
    exact Set.disjoint_left.1 hS₁S₂ hxS₁ hxS₂
  rcases d₁.subset_compactSide_or_subset_endSide hS₂conn.isPreconnected hS₂S₁ with
      hS₂B₁ | hS₂E₁
  · have hE₁S₂ : d₁.endSide ⊆ S₂ᶜ := by
      intro x hxE₁ hxS₂
      exact Set.disjoint_left.1 d₁.disjoint (hS₂B₁ hxS₂) hxE₁
    have hE₁E₂ : d₁.endSide ⊆ d₂.endSide :=
      d₂.subset_endSide_of_not_isCompact_closure
        d₁.isConnected_endSide.isPreconnected hE₁S₂
        d₁.not_isCompact_closure_endSide
    have hS₁E₂ : S₁ ⊆ d₂.endSide := by
      intro x hxS₁
      have hxclE₁ : x ∈ closure d₁.endSide := by
        apply frontier_subset_closure'
        simpa only [d₁.frontier_endSide] using hxS₁
      have hxclE₂ : x ∈ closure d₂.endSide := closure_mono hE₁E₂ hxclE₁
      rw [d₂.closure_endSide] at hxclE₂
      rcases hxclE₂ with hxE₂ | hxS₂
      · exact hxE₂
      · exact False.elim (Set.disjoint_left.1 hS₁S₂ hxS₁ hxS₂)
    have hB₂S₁ : d₂.compactSide ⊆ S₁ᶜ := by
      intro x hxB₂ hxS₁
      exact Set.disjoint_left.1 d₂.disjoint hxB₂ (hS₁E₂ hxS₁)
    have hB₂B₁ : d₂.compactSide ⊆ d₁.compactSide := by
      apply d₁.subset_compactSide_of_isPreconnected_of_inter_nonempty
        d₂.isConnected_compactSide.isPreconnected hB₂S₁
      obtain ⟨x, hxB₁, hxB₂⟩ := hBB
      exact ⟨x, hxB₂, hxB₁⟩
    have hK₂B₁ : closure d₂.compactSide ⊆ d₁.compactSide := by
      rw [d₂.closure_compactSide]
      exact union_subset hB₂B₁ hS₂B₁
    refine Or.inr ⟨hK₂B₁, ?_⟩
    intro hK₁B₂
    obtain ⟨x, hxS₂⟩ := hS₂conn.nonempty
    have hxB₁ : x ∈ d₁.compactSide := hS₂B₁ hxS₂
    have hxB₂ : x ∈ d₂.compactSide := hK₁B₂ (subset_closure hxB₁)
    exact d₂.compactSide_disjoint_sphere.le_bot ⟨hxB₂, hxS₂⟩
  · have hB₁S₂ : d₁.compactSide ⊆ S₂ᶜ := by
      intro x hxB₁ hxS₂
      exact Set.disjoint_left.1 d₁.disjoint hxB₁ (hS₂E₁ hxS₂)
    have hB₁B₂ : d₁.compactSide ⊆ d₂.compactSide :=
      d₂.subset_compactSide_of_isPreconnected_of_inter_nonempty
        d₁.isConnected_compactSide.isPreconnected hB₁S₂ hBB
    have hS₁B₂ : S₁ ⊆ d₂.compactSide := by
      intro x hxS₁
      have hxclB₁ : x ∈ closure d₁.compactSide := by
        apply frontier_subset_closure'
        simpa only [d₁.frontier_compactSide] using hxS₁
      have hxclB₂ : x ∈ closure d₂.compactSide := closure_mono hB₁B₂ hxclB₁
      rw [d₂.closure_compactSide] at hxclB₂
      rcases hxclB₂ with hxB₂ | hxS₂
      · exact hxB₂
      · exact False.elim (Set.disjoint_left.1 hS₁S₂ hxS₁ hxS₂)
    have hK₁B₂ : closure d₁.compactSide ⊆ d₂.compactSide := by
      rw [d₁.closure_compactSide]
      exact union_subset hB₁B₂ hS₁B₂
    refine Or.inl ⟨hK₁B₂, ?_⟩
    intro hK₂B₁
    obtain ⟨x, hxS₂⟩ := hS₂conn.nonempty
    have hxK₂ : x ∈ closure d₂.compactSide := by
      rw [d₂.closure_compactSide]
      exact Or.inr hxS₂
    have hxB₁ : x ∈ d₁.compactSide := hK₂B₁ hxK₂
    exact d₁.disjoint.le_bot ⟨hxB₁, hS₂E₁ hxS₂⟩

theorem disjoint_sides_strictly_nested
    (d₁ : SphereSides S₁) (d₂ : SphereSides S₂)
    (hS₁S₂ : Disjoint S₁ S₂) (hS₁conn : IsConnected S₁)
    (hS₂conn : IsConnected S₂)
    (hBB : (d₁.compactSide ∩ d₂.compactSide).Nonempty) :
    Xor
      (closure d₁.compactSide ⊂ d₂.compactSide ∧
        d₂.compactSide = interior (closure d₂.compactSide) ∧
        closure d₁.compactSide ⊂ closure d₂.compactSide)
      (closure d₂.compactSide ⊂ d₁.compactSide ∧
        d₁.compactSide = interior (closure d₁.compactSide) ∧
        closure d₂.compactSide ⊂ closure d₁.compactSide) := by
  rcases d₁.disjoint_sides_nested d₂ hS₁S₂ hS₂conn hBB with
      ⟨h₁₂, hn₂₁⟩ | ⟨h₂₁, hn₁₂⟩
  · have hs₁₂ : closure d₁.compactSide ⊂ d₂.compactSide := by
      refine ssubset_iff_subset_ne.mpr ⟨h₁₂, ?_⟩
      intro heq
      obtain ⟨x, hxS₂⟩ := hS₂conn.nonempty
      have hxcl₂ : x ∈ closure d₂.compactSide := by
        rw [d₂.closure_compactSide]
        exact Or.inr hxS₂
      have hxcl₁ : x ∈ closure d₁.compactSide := by
        rw [← heq, closure_closure] at hxcl₂
        exact hxcl₂
      exact d₂.compactSide_disjoint_sphere.le_bot ⟨h₁₂ hxcl₁, hxS₂⟩
    have hscl₁₂ : closure d₁.compactSide ⊂ closure d₂.compactSide := by
      refine ssubset_iff_subset_ne.mpr ⟨h₁₂.trans subset_closure, ?_⟩
      intro heq
      obtain ⟨x, hxS₂⟩ := hS₂conn.nonempty
      have hxcl₂ : x ∈ closure d₂.compactSide := by
        rw [d₂.closure_compactSide]
        exact Or.inr hxS₂
      rw [← heq] at hxcl₂
      exact d₂.compactSide_disjoint_sphere.le_bot ⟨h₁₂ hxcl₂, hxS₂⟩
    refine Or.inl ⟨⟨hs₁₂, d₂.interior_closure_compactSide.symm, hscl₁₂⟩, ?_⟩
    intro hreverse
    exact hn₂₁ hreverse.1.1
  · have hs₂₁ : closure d₂.compactSide ⊂ d₁.compactSide := by
      refine ssubset_iff_subset_ne.mpr ⟨h₂₁, ?_⟩
      intro heq
      obtain ⟨x, hxS₁⟩ := hS₁conn.nonempty
      have hxcl₁ : x ∈ closure d₁.compactSide := by
        rw [d₁.closure_compactSide]
        exact Or.inr hxS₁
      have hxcl₂ : x ∈ closure d₂.compactSide := by
        rw [← heq, closure_closure] at hxcl₁
        exact hxcl₁
      exact d₁.compactSide_disjoint_sphere.le_bot ⟨h₂₁ hxcl₂, hxS₁⟩
    have hscl₂₁ : closure d₂.compactSide ⊂ closure d₁.compactSide := by
      refine ssubset_iff_subset_ne.mpr ⟨h₂₁.trans subset_closure, ?_⟩
      intro heq
      obtain ⟨x, hxS₁⟩ := hS₁conn.nonempty
      have hxcl₁ : x ∈ closure d₁.compactSide := by
        rw [d₁.closure_compactSide]
        exact Or.inr hxS₁
      rw [← heq] at hxcl₁
      exact d₁.compactSide_disjoint_sphere.le_bot ⟨h₂₁ hxcl₁, hxS₁⟩
    refine Or.inr ⟨⟨hs₂₁, d₁.interior_closure_compactSide.symm, hscl₂₁⟩, ?_⟩
    intro hforward
    exact hn₁₂ hforward.1.1

end SphereSides

end DifferentialGeometry.Topology.SphereSeparation
