import Mathlib.Topology.Separation.Regular

section

open Set
open scoped Topology

theorem IsCompact.exists_finite_subcover_isCompact_closure
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [RegularSpace X]
    {K : Set X} (hK : IsCompact K) (U : K → Set X)
    (hU : ∀ x : K, U x ∈ 𝓝 (x : X)) :
    ∃ (t : Finset K) (W : K → Set X),
      (∀ x : K, IsOpen (W x) ∧ (x : X) ∈ W x ∧
        IsCompact (closure (W x)) ∧ closure (W x) ⊆ U x) ∧
      K ⊆ ⋃ x ∈ t, W x := by
  have hlocal (x : K) : ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U x := by
    obtain ⟨V, hVo, hxV, hVU, hVc⟩ :=
      exists_open_between_and_isCompact_closure
        (isCompact_singleton (x := (x : X))) isOpen_interior
        (singleton_subset_iff.mpr (mem_interior_iff_mem_nhds.mpr (hU x)))
    exact ⟨V, hVo, hxV (mem_singleton _), hVc, hVU.trans interior_subset⟩
  choose W hW using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W (fun x => (hW x).1)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (hW ⟨x, hx⟩).2.1⟩)
  exact ⟨t, W, hW, ht⟩

end
