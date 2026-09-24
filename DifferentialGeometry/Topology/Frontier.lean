import DifferentialGeometry.Topology.Combinatorics.BranchUpdates
import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.Basic

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

namespace DifferentialGeometry.Topology

open Set

theorem closure_interior_eq_of_frontier_subset_closure_interior
    {M : Type*} [TopologicalSpace M] {D : Set M} (hD : IsClosed D)
    (hfront : frontier D ⊆ closure (interior D)) : closure (interior D) = D := by
  apply Subset.antisymm hD.closure_interior_subset
  intro x hx
  by_cases hi : x ∈ interior D
  · exact subset_closure hi
  · exact hfront ((mem_frontier_iff_notMem_interior hx).mpr hi)

theorem eq_univ_of_recurrent_frontier_attachments
    {X Y ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Finite ι]
    (R B : ℕ → Set X) (hclosed : IsClosed (R 0)) (hne : (R 0).Nonempty)
    (hstep : ∀ n, R (n + 1) = R n ∪ B n)
    (face : ℕ → ι → Set X) (label : ℕ → ι)
    (hfrontier : ∀ n, frontier (R n) ⊆ ⋃ i, face n i)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hfilled : ∀ n, face n (label n) ⊆ interior (R (n + 1)))
    (hrecurrent : ∀ i N, ∃ n, N ≤ n ∧ label n = i)
    (ends : ι → Y → X) (hclosedRanges : ∀ i, IsClosed (range (ends i)))
    (hrange : ∀ i, range (ends i) = ⋃ n, ⋃ (_ : label n = i), B n) :
    (⋃ n, R n) = univ ∧ R 0 ∪ ⋃ i, range (ends i) = univ := by
  have hdecomposition : (⋃ n, R n) = R 0 ∪ ⋃ i, range (ends i) := by
    apply Subset.antisymm
    · apply iUnion_subset
      intro n
      induction n with
      | zero => exact subset_union_left
      | succ n ih =>
        rw [hstep n]
        refine union_subset ih ?_
        intro x hx
        right
        apply mem_iUnion.mpr
        refine ⟨label n, ?_⟩
        rw [hrange]
        exact mem_iUnion₂.mpr ⟨n, rfl, hx⟩
    · refine union_subset (subset_iUnion R 0) ?_
      apply iUnion_subset
      intro i
      rw [hrange]
      apply iUnion_subset
      intro n
      apply iUnion_subset
      intro hn
      have hsub : B n ⊆ R (n + 1) := (hstep n).symm ▸ subset_union_right
      exact hsub.trans (subset_iUnion R (n + 1))
  have hopen : IsOpen (⋃ n, R n) :=
    isOpen_iUnion_of_recurrent_frontier_updates R face label hfrontier hunchanged hfilled hrecurrent
  have hclosedall : IsClosed (⋃ n, R n) := by
    rw [hdecomposition]
    exact hclosed.union (isClosed_iUnion_of_finite hclosedRanges)
  have hfull : (⋃ n, R n) = univ :=
    (show IsClopen (⋃ n, R n) from ⟨hclosedall, hopen⟩).eq_univ
      (hne.mono (subset_iUnion R 0))
  exact ⟨hfull, hdecomposition.symm.trans hfull⟩

theorem eq_univ_of_recurrent_frontier_attachments_of_proper
    {X Y ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [Finite ι]
    (R B : ℕ → Set X) (hclosed : IsClosed (R 0)) (hne : (R 0).Nonempty)
    (hstep : ∀ n, R (n + 1) = R n ∪ B n)
    (face : ℕ → ι → Set X) (label : ℕ → ι)
    (hfrontier : ∀ n, frontier (R n) ⊆ ⋃ i, face n i)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hfilled : ∀ n, face n (label n) ⊆ interior (R (n + 1)))
    (hrecurrent : ∀ i N, ∃ n, N ≤ n ∧ label n = i)
    (ends : ι → Y → X) (hproper : ∀ i, IsProperMap (ends i))
    (hrange : ∀ i, range (ends i) = ⋃ n, ⋃ (_ : label n = i), B n) :
    (⋃ n, R n) = univ ∧ R 0 ∪ ⋃ i, range (ends i) = univ  := by
  exact eq_univ_of_recurrent_frontier_attachments R B hclosed hne hstep face label
    hfrontier hunchanged hfilled hrecurrent ends (fun i => (hproper i).isClosed_range) hrange

end DifferentialGeometry.Topology
