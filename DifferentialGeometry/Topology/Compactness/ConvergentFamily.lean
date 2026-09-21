import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open Set Filter
open scoped Topology

variable {X ι : Type*} [TopologicalSpace X]

theorem isCompact_insert_iUnion_of_eventually_subset {K : ι → Set X} {q : X}
    (hK : ∀ i, IsCompact (K i))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ i in cofinite, K i ⊆ U) :
    IsCompact (insert q (⋃ i, K i)) := by
  classical
  apply isCompact_iff_finite_subcover.mpr
  intro J U hU hcover
  obtain ⟨j, hqj⟩ := mem_iUnion.mp (hcover (mem_insert q _))
  have hfin : {i | ¬ K i ⊆ U j}.Finite := hlim (U j) ((hU j).mem_nhds hqj)
  have hcompact : IsCompact (⋃ i ∈ {i | ¬ K i ⊆ U j}, K i) :=
    hfin.isCompact_biUnion (fun i _ => hK i)
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U hU (by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxi⟩ := mem_iUnion.mp hi
    exact hcover (mem_insert_of_mem _ (mem_iUnion.mpr ⟨i, hxi⟩)))
  refine ⟨insert j s, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hqj⟩⟩
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    by_cases hi : K i ⊆ U j
    · exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hi hxi⟩⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp (hs (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩))
      obtain ⟨hks, hxk⟩ := mem_iUnion.mp hk
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hks, hxk⟩⟩
