/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLBall_union_of_inter_isPLBall_one_in_ball {B C D : Set E}
    (hB : IsPLBall 2 B) (hC : IsPLBall 2 C) (hD : IsPLBall 2 D)
    (hCB : C ⊆ B) (hDB : D ⊆ B) (hI : IsPLBall 1 (C ∩ D)) : IsPLBall 2 (C ∪ D) := by
  obtain ⟨R, _, _, _, hR, _⟩ := exists_isPLBall_pair_with_segment_inter
  obtain ⟨f, hf⟩ := hB
  obtain ⟨g, hg⟩ := hR
  have h := hf.symm.trans hg
  let u := g ∘ Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hu : IsPLHomeomorphOn u B R.space := h
  have hC' := hC.of_isPLHomeomorphOn (hu.restrict hC.isPolyhedron hCB)
  have hD' := hD.of_isPLHomeomorphOn (hu.restrict hD.isPolyhedron hDB)
  have hI' : IsPLBall 1 (u '' C ∩ u '' D) := by
    rw [← hu.bijOn.injOn.image_inter hCB hDB]
    exact hI.of_isPLHomeomorphOn (hu.restrict hI.isPolyhedron (inter_subset_left.trans hCB))
  have hleft := hD'.inter_subset_frontier_of_isPLBall hI' (by decide : 1 < 2)
  have hright : u '' C ∩ u '' D ⊆ frontier (u '' D) := by
    rw [inter_comm] at hI' ⊢
    exact hC'.inter_subset_frontier_of_isPLBall hI' (by decide : 1 < 2)
  have hball := (isPLBall_union_and_finite_frontier_inter hC' hD' hI' hleft hright).1
  rw [← image_union] at hball
  exact hball.of_isPLHomeomorphOn
    (hu.restrict (hC.isPolyhedron.union hD.isPolyhedron) (union_subset hCB hDB)).symm

theorem isPLBall_union_iUnion_of_pairwiseDisjoint_in_ball {ι : Type*}
    {B C : Set E} (hB : IsPLBall 2 B) (hC : IsPLBall 2 C) (hCB : C ⊆ B)
    (d : Finset ι) (A : ι → Set E) (hA : ∀ i ∈ d, IsPLBall 2 (A i))
    (hAB : ∀ i ∈ d, A i ⊆ B) (hI : ∀ i ∈ d, IsPLBall 1 (C ∩ A i))
    (hdis : ∀ i ∈ d, ∀ j ∈ d, i ≠ j → Disjoint (A i) (A j)) :
    IsPLBall 2 (C ∪ ⋃ i ∈ d, A i) := by
  classical
  induction d using Finset.induction_on with
  | empty => simpa using hC
  | @insert i d hi ih =>
    have hA' : ∀ j ∈ d, IsPLBall 2 (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hAB' : ∀ j ∈ d, A j ⊆ B := fun j hj => hAB j (Finset.mem_insert_of_mem hj)
    have hI' : ∀ j ∈ d, IsPLBall 1 (C ∩ A j) := fun j hj => hI j (Finset.mem_insert_of_mem hj)
    have hdis' : ∀ j ∈ d, ∀ k ∈ d, j ≠ k → Disjoint (A j) (A k) :=
      fun j hj k hk hjk => hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hprev := ih hA' hAB' hI' hdis'
    have hprevB : (C ∪ ⋃ j ∈ d, A j) ⊆ B :=
      union_subset hCB (iUnion₂_subset hAB')
    have hinter : (C ∪ ⋃ j ∈ d, A j) ∩ A i = C ∩ A i := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxi⟩
        · exact ⟨hx, hxi⟩
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
          exact ((hdis j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
            (ne_of_mem_of_not_mem hj hi)).le_bot ⟨hxj, hxi⟩).elim
      · rintro x ⟨hx, hxi⟩
        exact ⟨Or.inl hx, hxi⟩
    have h := isPLBall_union_of_inter_isPLBall_one_in_ball hB hprev
      (hA i (Finset.mem_insert_self _ _)) hprevB (hAB i (Finset.mem_insert_self _ _))
      (hinter.symm ▸ hI i (Finset.mem_insert_self _ _))
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

end DifferentialGeometry.Topology.PiecewiseLinear
