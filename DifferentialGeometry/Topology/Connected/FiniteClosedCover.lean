import Mathlib.Topology.Connected.Clopen

open Set

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

theorem IsPreconnected.subset_of_subset_iUnion_disjoint_closed
    {S : Set X} (hS : IsPreconnected S) {C : ι → Set X}
    (hC : ∀ i, IsClosed (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : S ⊆ ⋃ i, C i) {i : ι} (hmeet : (S ∩ C i).Nonempty) : S ⊆ C i := by
  let V := ⋃ j : {j : ι // j ≠ i}, C j.val
  have hV : IsClosed V := isClosed_iUnion_of_finite fun j => hC j.val
  have hUV : Disjoint (C i) V := by
    apply disjoint_left.mpr
    intro x hx hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    exact disjoint_left.mp (hdisj j.property.symm) hx hj
  have hsub : S ⊆ C i ∪ V := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  obtain h | h := isPreconnected_iff_subset_of_disjoint_closed.mp hS
    (C i) V (hC i) hV hsub (by rw [hUV.inter_eq, inter_empty])
  · exact h
  · obtain ⟨x, hx, hxi⟩ := hmeet
    exact False.elim (disjoint_left.mp hUV hxi (h hx))

theorem IsConnected.exists_unique_subset_of_iUnion_disjoint_closed
    {S : Set X} (hS : IsConnected S) {C : ι → Set X}
    (hC : ∀ i, IsClosed (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : S ⊆ ⋃ i, C i) : ∃! i, S ⊆ C i := by
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  refine ⟨i, hS.isPreconnected.subset_of_subset_iUnion_disjoint_closed hC hdisj hcover
    ⟨x, hx, hxi⟩, ?_⟩
  intro j hj
  by_contra hji
  exact disjoint_left.mp (hdisj hji) (hj hx) hxi
