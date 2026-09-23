import DifferentialGeometry.Topology.Combinatorics.BranchUpdates
import Mathlib.Topology.Closure

namespace DifferentialGeometry.Topology

open Set

theorem frontier_union_eq_sdiff_closure_of_frontier_subset_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = frontier A \ closure B := by
  apply Subset.antisymm
  · intro x hx
    have hxA : x ∈ frontier A := by
      rcases frontier_union_subset A B hx with hA | hB'
      · exact hA.1
      · exact False.elim (hx.2 (interior_mono subset_union_left (hB hB'.2)))
    refine ⟨hxA, ?_⟩
    intro hxB
    apply hxA.2 (hB ⟨hxB, ?_⟩)
    intro hxBi
    exact hx.2 (interior_mono subset_union_right hxBi)
  · rintro x ⟨hxA, hxB⟩
    refine ⟨closure_mono subset_union_left hxA.1, ?_⟩
    intro hx
    apply hxA.2
    apply mem_interior.mpr
    refine ⟨interior (A ∪ B) ∩ (closure B)ᶜ, ?_,
      isOpen_interior.inter isClosed_closure.isOpen_compl, hx, hxB⟩
    intro y hy
    exact (interior_subset hy.1).resolve_right (fun h ↦ hy.2 (subset_closure h))

theorem frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hclosed : IsClosed B) (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = frontier A \ B := by
  rw [frontier_union_eq_sdiff_closure_of_frontier_subset_interior hB, hclosed.closure_eq]

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

theorem isOpen_iUnion_of_recurrent_frontier_updates
    {M ι : Type*} [TopologicalSpace M]
    (W : ℕ → Set M) (face : ℕ → ι → Set M) (label : ℕ → ι)
    (hfrontier : ∀ n, frontier (W n) ⊆ ⋃ i, face n i)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (hrecurrent : ∀ i N, ∃ n, N ≤ n ∧ label n = i) :
    IsOpen (⋃ n, W n) := by
  classical
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  have hxi : ∃ k, x ∈ interior (W k) := by
    by_cases hint : x ∈ interior (W n)
    · exact ⟨n, hint⟩
    have hxf : x ∈ frontier (W n) := (mem_frontier_iff_notMem_interior hxn).mpr hint
    obtain ⟨i, hface⟩ := Set.mem_iUnion.mp (hfrontier n hxf)
    have hex : ∃ k, n ≤ k ∧ label k = i := hrecurrent i n
    have hk := Nat.find_spec hex
    have heq : face (Nat.find hex) i = face n i :=
      eq_of_no_update_between label face hunchanged i hk.1 (by
        intro m hnm hmk hm
        exact Nat.find_min hex hmk ⟨hnm, hm⟩)
    refine ⟨Nat.find hex + 1, hfilled _ ?_⟩
    rw [hk.2, heq]
    exact hface
  obtain ⟨k, hk⟩ := hxi
  exact ⟨interior (W k), interior_subset.trans (Set.subset_iUnion W k), isOpen_interior, hk⟩

end DifferentialGeometry.Topology
