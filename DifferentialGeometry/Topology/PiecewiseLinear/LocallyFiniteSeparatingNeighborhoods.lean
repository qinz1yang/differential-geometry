/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isOpen_inter_subset_interior_of_locallyFinite {X ι : Type*} [MetricSpace X]
    {A : ι → Set X} (hA : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) {Z : Set X}
    (hAZ : ∀ i j, i ≠ j → A i ∩ A j ⊆ interior Z) {G : ι → Set X} (hG : ∀ i, IsOpen (G i))
    (hAG : ∀ i, A i ⊆ G i) :
    ∃ W : ι → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, A i ⊆ W i) ∧ (∀ i, W i ⊆ G i) ∧
      ∀ i j, i ≠ j → W i ∩ W j ⊆ interior Z := by
  classical
  let E : ι → Set X := fun i => A i \ interior Z
  have hEc : ∀ i, IsClosed (E i) := fun i => (hA i).sdiff isOpen_interior
  have hEloc : LocallyFinite E := hloc.subset fun i => sdiff_subset
  let F : ι → Set X := fun i => ⋃ j : {j // j ≠ i}, E j
  have hFc : ∀ i, IsClosed (F i) := fun i =>
    (hEloc.comp_injective Subtype.val_injective).isClosed_iUnion fun j => hEc j
  have hEF : ∀ i j, j ≠ i → E j ⊆ F i := fun i j hji =>
    subset_iUnion (fun j : {j // j ≠ i} => E j) ⟨j, hji⟩
  have hdisj : ∀ i, Disjoint (E i) (F i) := by
    intro i
    rw [Set.disjoint_left]
    intro x hxi hxF
    obtain ⟨⟨j, hji⟩, hxj⟩ := mem_iUnion.mp hxF
    exact hxi.2 (hAZ i j hji.symm ⟨hxi.1, hxj.1⟩)
  let O : ι → Set X := fun i =>
    if (E i).Nonempty then
      (if (F i).Nonempty then {x | infDist x (E i) < infDist x (F i)} else univ)
    else ∅
  have hOo : ∀ i, IsOpen (O i) := by
    intro i
    simp only [O]
    split_ifs
    · exact isOpen_lt (continuous_infDist_pt _) (continuous_infDist_pt _)
    · exact isOpen_univ
    · exact isOpen_empty
  have hEO : ∀ i, E i ⊆ O i := by
    intro i x hx
    have hne : (E i).Nonempty := ⟨x, hx⟩
    simp only [O, ite_eq_left hne]
    split_ifs with hF
    · change infDist x (E i) < infDist x (F i)
      rw [infDist_zero_of_mem hx]
      apply (infDist_pos_iff_notMem_closure hF).mp
      rw [(hFc i).closure_eq]
      exact Set.disjoint_left.mp (hdisj i) hx
    · exact mem_univ x
  have hOO : ∀ i j, i ≠ j → ∀ x, x ∈ O i → x ∉ O j := by
    intro i j hij x hi hj
    by_cases hEi : (E i).Nonempty
    · by_cases hEj : (E j).Nonempty
      · have hFi : (F i).Nonempty := hEj.mono (hEF i j hij.symm)
        have hFj : (F j).Nonempty := hEi.mono (hEF j i hij)
        simp only [O, ite_eq_left hEi, ite_eq_left hFi] at hi
        simp only [O, ite_eq_left hEj, ite_eq_left hFj] at hj
        have h1 : infDist x (F i) ≤ infDist x (E j) :=
          infDist_le_infDist_of_subset (hEF i j hij.symm) hEj
        have h2 : infDist x (F j) ≤ infDist x (E i) :=
          infDist_le_infDist_of_subset (hEF j i hij) hEi
        have hi' : infDist x (E i) < infDist x (F i) := hi
        have hj' : infDist x (E j) < infDist x (F j) := hj
        linarith
      · simp only [O, ite_eq_right hEj] at hj
        exact hj
    · simp only [O, ite_eq_right hEi] at hi
      exact hi
  refine ⟨fun i => (O i ∪ interior Z) ∩ G i,
    fun i => ((hOo i).union isOpen_interior).inter (hG i), fun i x hx => ⟨?_, hAG i hx⟩,
    fun i => inter_subset_right, ?_⟩
  · by_cases hxZ : x ∈ interior Z
    · exact Or.inr hxZ
    · exact Or.inl (hEO i ⟨hx, hxZ⟩)
  · rintro i j hij x ⟨⟨hi | hi, -⟩, ⟨hj | hj, -⟩⟩
    · exact absurd hj (hOO i j hij x hi)
    · exact hj
    · exact hi
    · exact hi

end DifferentialGeometry.Topology.PiecewiseLinear
