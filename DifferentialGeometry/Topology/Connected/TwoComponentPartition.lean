import Mathlib.Topology.Connected.Basic

open Set

namespace Poincare.Topology

theorem subset_or_subset_of_isPreconnected_of_isClosed
    {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v)
    (hd : Disjoint u v) (hsub : s ⊆ u ∪ v) : s ⊆ u ∨ s ⊆ v := by
  classical
  by_cases hsu : s ⊆ u
  · exact Or.inl hsu
  · obtain ⟨x, hxs, hxu⟩ := Set.not_subset.mp hsu
    refine Or.inr fun y hys ↦ ?_
    by_contra hyv
    obtain ⟨z, _, hzu, hzv⟩ := isPreconnected_closed_iff.mp hs u v hu hv hsub
      ⟨y, hys, (hsub hys).resolve_right hyv⟩
      ⟨x, hxs, (hsub hxs).resolve_left hxu⟩
    exact hd.notMem_of_mem_left hzu hzv

private theorem eq_pair_of_subsets_of_union_eq_union
    {X : Type*} {A₀ A₁ B₀ B₁ : Set X}
    (hd : Disjoint B₀ B₁) (hcover : A₀ ∪ A₁ = B₀ ∪ B₁)
    (h₀ : A₀ ⊆ B₀) (h₁ : A₁ ⊆ B₁) : A₀ = B₀ ∧ A₁ = B₁ := by
  constructor
  · refine Subset.antisymm h₀ fun x hx ↦ ?_
    rcases hcover.symm.subset (Or.inl hx) with hxA | hxA
    · exact hxA
    · exact False.elim (hd.notMem_of_mem_left hx (h₁ hxA))
  · refine Subset.antisymm h₁ fun x hx ↦ ?_
    rcases hcover.symm.subset (Or.inr hx) with hxA | hxA
    · exact False.elim (hd.notMem_of_mem_left (h₀ hxA) hx)
    · exact hxA

theorem eq_or_eq_of_two_preconnected_closed_partitions
    {X : Type*} [TopologicalSpace X] {A₀ A₁ B₀ B₁ : Set X}
    (hA₀ : IsPreconnected A₀) (hA₁ : IsPreconnected A₁)
    (hB₀ : B₀.Nonempty) (hB₁ : B₁.Nonempty)
    (hc₀ : IsClosed B₀) (hc₁ : IsClosed B₁)
    (hd : Disjoint B₀ B₁) (hcover : A₀ ∪ A₁ = B₀ ∪ B₁) :
    (A₀ = B₀ ∧ A₁ = B₁) ∨ (A₀ = B₁ ∧ A₁ = B₀) := by
  have hsub₀ : A₀ ⊆ B₀ ∪ B₁ := subset_union_left.trans hcover.subset
  have hsub₁ : A₁ ⊆ B₀ ∪ B₁ := subset_union_right.trans hcover.subset
  rcases subset_or_subset_of_isPreconnected_of_isClosed hA₀ hc₀ hc₁ hd hsub₀ with h₀ | h₀
  · rcases subset_or_subset_of_isPreconnected_of_isClosed hA₁ hc₀ hc₁ hd hsub₁ with h₁ | h₁
    · obtain ⟨x, hx⟩ := hB₁
      have hxB₀ : x ∈ B₀ := (hcover.symm.subset (Or.inr hx)).elim (fun h ↦ h₀ h) (fun h ↦ h₁ h)
      exact False.elim (hd.notMem_of_mem_left hxB₀ hx)
    · exact Or.inl (eq_pair_of_subsets_of_union_eq_union hd hcover h₀ h₁)
  · rcases subset_or_subset_of_isPreconnected_of_isClosed hA₁ hc₀ hc₁ hd hsub₁ with h₁ | h₁
    · exact Or.inr (eq_pair_of_subsets_of_union_eq_union hd.symm
        (hcover.trans (union_comm B₀ B₁)) h₀ h₁)
    · obtain ⟨x, hx⟩ := hB₀
      have hxB₁ : x ∈ B₁ := (hcover.symm.subset (Or.inl hx)).elim (fun h ↦ h₀ h) (fun h ↦ h₁ h)
      exact False.elim (hd.notMem_of_mem_left hx hxB₁)

end Poincare.Topology
