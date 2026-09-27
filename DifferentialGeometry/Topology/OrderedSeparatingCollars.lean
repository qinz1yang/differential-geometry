import Mathlib.Topology.Connected.Basic

open Set Topology

namespace DifferentialGeometry.Topology

private theorem subset_left_of_closed_disjoint_cover
    {X : Type*} [TopologicalSpace X] {A P Q : Set X}
    (hA : IsPreconnected A) (hP : IsClosed P) (hQ : IsClosed Q)
    (hPQ : Disjoint P Q) (hcover : A ⊆ P ∪ Q)
    (hmeet : (A ∩ P).Nonempty) : A ⊆ P := by
  intro x hx
  rcases hcover hx with hp | hq
  · exact hp
  · obtain ⟨y, _, hyP, hyQ⟩ :=
      isPreconnected_closed_iff.mp hA P Q hP hQ hcover hmeet ⟨x, hx, hq⟩
    exact False.elim (Set.disjoint_left.mp hPQ hyP hyQ)

private theorem subset_interior_of_disjoint_closed_complement
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hC : IsClosed C) (hcover : B ∪ C = univ) (hdisj : Disjoint A C) :
    A ⊆ interior B := by
  intro x hx
  have hxC : x ∉ C := fun hc ↦ Set.disjoint_left.mp hdisj hx hc
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hC.isOpen_compl.mem_nhds hxC)
  intro y hy
  exact (show y ∈ B ∪ C from hcover.symm ▸ mem_univ y).resolve_right hy

theorem ordered_exteriors_of_disjoint_separating_collars
    {X : Type*} [TopologicalSpace X]
    (P₀ K₀ Q₀ P₁ K₁ Q₁ : Set X)
    (hP₀ : IsClosed P₀) (hK₀ : IsClosed K₀) (hQ₀ : IsClosed Q₀)
    (hP₁ : IsClosed P₁) (hK₁ : IsClosed K₁) (hQ₁ : IsClosed Q₁)
    (hcover₀ : P₀ ∪ K₀ ∪ Q₀ = univ) (hcover₁ : P₁ ∪ K₁ ∪ Q₁ = univ)
    (hdisj₀ : Disjoint P₀ Q₀) (hdisj₁ : Disjoint P₁ Q₁)
    (hcollars : Disjoint K₀ K₁)
    (hconn₀ : IsPreconnected K₀) (hconn₁ : IsPreconnected (K₁ ∪ Q₁))
    (horder : (K₀ ∩ P₁).Nonempty) (hupper : (Q₀ ∩ Q₁).Nonempty) :
    P₀ ∪ K₀ ⊆ interior P₁ ∧ K₁ ∪ Q₁ ⊆ interior Q₀ ∧
      interior Q₀ ∪ interior P₁ = univ := by
  have hK₀P₁ : K₀ ⊆ P₁ := by
    apply subset_left_of_closed_disjoint_cover hconn₀ hP₁ hQ₁ hdisj₁ _ horder
    intro x hx
    have hxK₁ : x ∉ K₁ := fun hy ↦ Set.disjoint_left.mp hcollars hx hy
    rcases (show x ∈ P₁ ∪ K₁ ∪ Q₁ from hcover₁.symm ▸ mem_univ x) with (hp | hk) | hq
    · exact Or.inl hp
    · exact False.elim (hxK₁ hk)
    · exact Or.inr hq
  have havoid : Disjoint K₀ (K₁ ∪ Q₁) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hy with hk | hq
    · exact Set.disjoint_left.mp hcollars hx hk
    · exact Set.disjoint_left.mp hdisj₁ (hK₀P₁ hx) hq
  have hright : K₁ ∪ Q₁ ⊆ Q₀ := by
    apply subset_left_of_closed_disjoint_cover hconn₁ hQ₀ hP₀ hdisj₀.symm
    · intro x hx
      have hxK₀ : x ∉ K₀ := fun hy ↦ Set.disjoint_left.mp havoid hy hx
      rcases (show x ∈ P₀ ∪ K₀ ∪ Q₀ from hcover₀.symm ▸ mem_univ x) with (hp | hk) | hq
      · exact Or.inr hp
      · exact False.elim (hxK₀ hk)
      · exact Or.inl hq
    · obtain ⟨x, hx₀, hx₁⟩ := hupper
      exact ⟨x, Or.inr hx₁, hx₀⟩
  have hdisjoint : Disjoint (P₀ ∪ K₀) (K₁ ∪ Q₁) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hp | hk
    · exact Set.disjoint_left.mp hdisj₀ hp (hright hy)
    · exact Set.disjoint_left.mp havoid hk hy
  have hleftInt : P₀ ∪ K₀ ⊆ interior P₁ :=
    subset_interior_of_disjoint_closed_complement (hK₁.union hQ₁)
      (union_assoc P₁ K₁ Q₁ ▸ hcover₁) hdisjoint
  have hrightInt : K₁ ∪ Q₁ ⊆ interior Q₀ :=
    subset_interior_of_disjoint_closed_complement (hP₀.union hK₀)
      (union_comm Q₀ (P₀ ∪ K₀) ▸ hcover₀) hdisjoint.symm
  refine ⟨hleftInt, hrightInt, eq_univ_of_forall fun x ↦ ?_⟩
  by_cases hx : x ∈ K₁ ∪ Q₁
  · exact Or.inl (hrightInt hx)
  · apply Or.inr
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset ((hK₁.union hQ₁).isOpen_compl.mem_nhds hx)
    intro y hy
    have hycover : y ∈ P₁ ∪ (K₁ ∪ Q₁) := by
      rw [← union_assoc, hcover₁]
      exact mem_univ y
    exact hycover.resolve_right hy

end DifferentialGeometry.Topology
