import DifferentialGeometry.Topology.SphereSeparation.Nesting

namespace DifferentialGeometry.Topology.SphereSeparation.SphereSides

open Set

variable {X : Type*} [TopologicalSpace X] {S S₀ S₁ : Set X}

theorem closure_compactSide_eq_compl (d : SphereSides S) : closure d.compactSide = d.endSideᶜ := by
  rw [d.closure_compactSide]
  ext x
  constructor
  · rintro (hx | hx)
    · exact fun h ↦ d.disjoint.le_bot ⟨hx, h⟩
    · exact fun h ↦ d.endSide_disjoint_sphere.le_bot ⟨h, hx⟩
  · intro hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hm : x ∈ d.compactSide ∪ d.endSide := d.compl_eq_union ▸ hxS
      exact Or.inl (hm.resolve_right hx)

theorem closure_endSide_eq_compl (d : SphereSides S) : closure d.endSide = d.compactSideᶜ := by
  rw [d.closure_endSide]
  ext x
  constructor
  · rintro (hx | hx)
    · exact fun h ↦ d.disjoint.le_bot ⟨h, hx⟩
    · exact fun h ↦ d.compactSide_disjoint_sphere.le_bot ⟨h, hx⟩
  · intro hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hm : x ∈ d.compactSide ∪ d.endSide := d.compl_eq_union ▸ hxS
      exact Or.inl (hm.resolve_left hx)

theorem closure_compactSide_subset_of_sphere_subset
    (d₀ : SphereSides S₀) (d₁ : SphereSides S₁) (hd : Disjoint S₀ S₁)
    (hS₁ : IsConnected S₁) (hsub : S₁ ⊆ d₀.compactSide) :
    closure d₁.compactSide ⊆ d₀.compactSide := by
  obtain ⟨x, hx⟩ := hS₁.nonempty
  have hxc : x ∈ closure d₁.compactSide := by
    rw [d₁.closure_compactSide]
    exact Or.inr hx
  obtain ⟨y, hy₀, hy₁⟩ := mem_closure_iff.mp hxc d₀.compactSide
    d₀.isOpen_compactSide (hsub hx)
  rcases d₀.disjoint_sides_nested d₁ hd hS₁ ⟨y, hy₀, hy₁⟩ with h | h
  · exact False.elim (d₁.compactSide_disjoint_sphere.le_bot
      ⟨h.1 (subset_closure (hsub hx)), hx⟩)
  · exact h.1

end DifferentialGeometry.Topology.SphereSeparation.SphereSides
