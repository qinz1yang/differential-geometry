/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.Separation

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem separates_frontier {C H K : Set X}
    (hH : H ⊆ interior C) (hK : K ⊆ interior Cᶜ) : Separates (frontier C) H K := by
  refine ⟨interior C, interior Cᶜ, isOpen_interior, isOpen_interior,
    disjoint_compl_right.mono interior_subset interior_subset,
    compl_frontier_eq_union_interior.symm, hH, hK⟩

theorem Separates.inter_nonempty_of_isPreconnected {C H K A : Set X}
    (h : Separates C H K) (hA : IsPreconnected A)
    (hHA : (H ∩ A).Nonempty) (hKA : (K ∩ A).Nonempty) : (C ∩ A).Nonempty := by
  classical
  obtain ⟨U, V, hU, hV, hd, hUV, hH, hK⟩ := h
  obtain ⟨x, hxH, hxA⟩ := hHA
  obtain ⟨y, hyK, hyA⟩ := hKA
  by_contra hn
  have hsub : A ⊆ U ∪ V := by
    intro z hz
    rw [hUV]
    exact fun hzC => hn ⟨z, hzC, hz⟩
  obtain ⟨z, -, hzU, hzV⟩ :=
    hA U V hU hV hsub ⟨x, hxA, hH hxH⟩ ⟨y, hyA, hK hyK⟩
  exact disjoint_left.mp hd hzU hzV

theorem Separates.subset_interior_of_disjoint_frontier {C H K A : Set X}
    (h : Separates C H K) (hC : IsPreconnected C) (hA : IsPreconnected A)
    (hHA : (H ∩ A).Nonempty) (hKA : (K ∩ A).Nonempty)
    (hd : Disjoint C (frontier A)) : C ⊆ interior A := by
  obtain ⟨x, hxC, hxA⟩ := h.inter_nonempty_of_isPreconnected hA hHA hKA
  have hxI : x ∈ interior A := by
    by_contra hn
    exact disjoint_left.mp hd hxC ⟨subset_closure hxA, hn⟩
  apply hC.subset_left_of_subset_union isOpen_interior isOpen_interior
    (disjoint_compl_right.mono interior_subset interior_subset) _ ⟨x, hxC, hxI⟩
  rw [← compl_frontier_eq_union_interior]
  exact disjoint_left.mp hd

end DifferentialGeometry.Topology
