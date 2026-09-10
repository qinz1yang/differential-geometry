import DifferentialGeometry.Topology.Connected.CollarCover

open Set Topology

namespace Poincare.Topology

private theorem frontier_left_subset_inter_of_closed_cover
    {X : Type*} [TopologicalSpace X] {P K Q : Set X}
    (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q) :
    frontier P ⊆ P ∩ K := by
  intro x hx
  have hxP : x ∈ P := hP.frontier_subset hx
  refine ⟨hxP, ?_⟩
  by_contra hxK
  apply hx.2
  apply mem_interior_iff_mem_nhds.mpr
  have hxavoid : x ∉ K ∪ Q := by
    rintro (hk | hq)
    · exact hxK hk
    · exact Set.disjoint_left.mp hdisj hxP hq
  apply Filter.mem_of_superset ((hK.union hQ).isOpen_compl.mem_nhds hxavoid)
  intro y hy
  rcases (show y ∈ P ∪ K ∪ Q from hcover.symm ▸ mem_univ y) with (hp | hk) | hq
  · exact hp
  · exact False.elim (hy (Or.inl hk))
  · exact False.elim (hy (Or.inr hq))

private theorem left_subset_interior_union_of_collar_subset
    {X : Type*} [TopologicalSpace X] {P K Q D : Set X}
    (hQ : IsClosed Q) (hcover : P ∪ K ∪ Q = univ)
    (hdisj : Disjoint P Q) (hKD : K ⊆ D) : P ⊆ interior (P ∪ D) := by
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  have hxQ : x ∉ Q := fun hq ↦ Set.disjoint_left.mp hdisj hx hq
  apply Filter.mem_of_superset (hQ.isOpen_compl.mem_nhds hxQ)
  intro y hy
  rcases (show y ∈ P ∪ K ∪ Q from hcover.symm ▸ mem_univ y) with (hp | hk) | hq
  · exact Or.inl hp
  · exact Or.inr (hKD hk)
  · exact False.elim (hy hq)

theorem cover_and_between_subset_of_separating_collars
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (P₀ K₀ Q₀ P₁ K₁ Q₁ D : Set X)
    (hP₀ : IsClosed P₀) (hK₀ : IsClosed K₀) (hQ₀ : IsClosed Q₀)
    (hP₁ : IsClosed P₁) (hK₁ : IsClosed K₁) (hQ₁ : IsClosed Q₁)
    (hcover₀ : P₀ ∪ K₀ ∪ Q₀ = univ) (hcover₁ : P₁ ∪ K₁ ∪ Q₁ = univ)
    (hdisj₀ : Disjoint P₀ Q₀) (hdisj₁ : Disjoint P₁ Q₁)
    (hne : K₀.Nonempty) (hK₀D : K₀ ⊆ D) (hK₁D : K₁ ⊆ D)
    (hfront : frontier D ⊆ (P₀ ∩ K₀) ∪ (K₁ ∩ Q₁)) :
    P₀ ∪ D ∪ Q₁ = univ ∧ (interior P₀)ᶜ ∩ (interior Q₁)ᶜ ⊆ D := by
  have hcover₁' : Q₁ ∪ K₁ ∪ P₁ = univ := by
    simpa only [union_comm, union_left_comm, union_assoc] using hcover₁
  have hfrontP : frontier P₀ ⊆ P₀ ∩ K₀ :=
    frontier_left_subset_inter_of_closed_cover hP₀ hK₀ hQ₀ hcover₀ hdisj₀
  have hfrontQ : frontier Q₁ ⊆ K₁ ∩ Q₁ := by
    simpa only [inter_comm] using
      frontier_left_subset_inter_of_closed_cover hQ₁ hK₁ hP₁ hcover₁' hdisj₁.symm
  have hleft : P₀ ∩ K₀ ⊆ interior (P₀ ∪ D) :=
    inter_subset_left.trans
      (left_subset_interior_union_of_collar_subset hQ₀ hcover₀ hdisj₀ hK₀D)
  have hright : K₁ ∩ Q₁ ⊆ interior (D ∪ Q₁) := by
    rw [union_comm D Q₁]
    exact inter_subset_right.trans
      (left_subset_interior_union_of_collar_subset hP₁ hcover₁' hdisj₁.symm hK₁D)
  exact cover_and_between_subset_of_frontier_sections P₀ D Q₁ (P₀ ∩ K₀) (K₁ ∩ Q₁)
    hfrontP hfront hfrontQ (inter_subset_right.trans hK₀D) (inter_subset_left.trans hK₁D)
    hleft hright (hne.mono (fun _ hx ↦ Or.inl (Or.inr (hK₀D hx))))

end Poincare.Topology
