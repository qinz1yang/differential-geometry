/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLBall_union_iUnion_of_disk_intersections {ι : Type*} {R : Set E3}
    (hR : IsPLBall 3 R) (s : Finset ι) (A : ι → Set E3)
    (hA : ∀ i ∈ s, IsPLBall 3 (A i))
    (hAR : ∀ i ∈ s, IsPLBall 2 (A i ∩ R))
    (hAA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsPLBall 2 (A i ∩ A j))
    (hARA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsPLBall 1 ((A i ∩ R) ∩ A j))
    (htriple : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
      i ≠ j → i ≠ k → j ≠ k → (A i ∩ A j) ∩ A k = ∅) :
    IsPLBall 3 (R ∪ ⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hR
  | @insert i s hi ih =>
    have hm (j : ι) (hj : j ∈ s) : j ∈ insert i s := Finset.mem_insert_of_mem hj
    have hi' : i ∈ insert i s := Finset.mem_insert_self _ _
    have hij (j : ι) (hj : j ∈ s) : i ≠ j := fun h => hi (h.symm ▸ hj)
    have hprev := ih (fun j hj => hA j (hm j hj)) (fun j hj => hAR j (hm j hj))
      (fun j hj k hk hne => hAA j (hm j hj) k (hm k hk) hne)
      (fun j hj k hk hne => hARA j (hm j hj) k (hm k hk) hne)
      (fun j hj k hk l hl hjk hjl hkl =>
        htriple j (hm j hj) k (hm k hk) l (hm l hl) hjk hjl hkl)
    have hiBall := hA i hi'
    have hiSphere := hiBall.isPLSphere_frontier
    obtain ⟨K, hKfin, hKspace⟩ := hiSphere.isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hKfin.to_subtype
    have hKSphere : IsPLSphere 2 K.space := hKspace.symm ▸ hiSphere
    have hK : IsCombinatorialManifoldWithBoundary 2 K :=
      (IsPLSphere.isCombinatorialManifold (n := 1) hKSphere).isCombinatorialManifoldWithBoundary
    have hPK : A i ∩ R ⊆ K.space :=
      (hR.inter_subset_frontier_of_isPLBall (hAR i hi') (by decide)).trans hKspace.symm.subset
    let D : ι → Set E3 := fun j => A i ∩ A j
    have hD (j : ι) (hj : j ∈ s) : IsPLBall 2 (D j) :=
      hAA i hi' j (hm j hj) (hij j hj)
    have hDK (j : ι) (hj : j ∈ s) : D j ⊆ K.space :=
      ((hA j (hm j hj)).inter_subset_frontier_of_isPLBall (hD j hj) (by decide)).trans
        hKspace.symm.subset
    have hPD (j : ι) (hj : j ∈ s) : IsPLBall 1 ((A i ∩ R) ∩ D j) := by
      have heq : (A i ∩ R) ∩ D j = (A i ∩ R) ∩ A j := by
        ext x
        simp only [D, mem_inter_iff]
        tauto
      rw [heq]
      exact hARA i hi' j (hm j hj) (hij j hj)
    have hdis (j : ι) (hj : j ∈ s) (k : ι) (hk : k ∈ s) (hjk : j ≠ k) :
        Disjoint (D j) (D k) := by
      rw [Set.disjoint_left]
      intro x hxj hxk
      exact (eq_empty_iff_forall_notMem.mp
        (htriple i hi' j (hm j hj) k (hm k hk) (hij j hj) (hij k hk) hjk))
        x ⟨hxj, hxk.2⟩
    have hattach := hK.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface
      (hAR i hi') hPK s D hD hDK hPD hdis
    have hmeet : IsPLBall 2 (A i ∩ (R ∪ ⋃ j ∈ s, A j)) := by
      simpa only [inter_union_distrib_left, inter_iUnion, D] using hattach
    have hmeet' : IsPLBall 2 ((R ∪ ⋃ j ∈ s, A j) ∩ A i) := by
      simpa only [inter_comm] using hmeet
    have hball := isPLBall_union_of_inter_isPLBall_two hiBall hprev hmeet
      (hprev.inter_subset_frontier_of_isPLBall hmeet (by decide))
      (fun x hx => hiBall.inter_subset_frontier_of_isPLBall hmeet' (by decide) ⟨hx.2, hx.1⟩)
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using hball

end DifferentialGeometry.Topology.PiecewiseLinear
