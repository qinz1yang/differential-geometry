/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactClawBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}

theorem IsPLCellOn.union_of_inter_eq_of_subset_frontier_in_chart
    {B BB V VB S SB : Set M} (hB : IsPLCellOn 3 B BB) (hV : IsPLCellOn 3 V VB)
    (hS : IsPLCellOn 2 S SB) (hBV : B ∩ V = S) (hSV : S ⊆ frontier V)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hBc : B ⊆ c.source) (hVc : V ⊆ c.source) :
    IsPLCellOn 3 (B ∪ V) (frontier (B ∪ V)) := by
  obtain ⟨hBi, -⟩ := hB.isPLBall_image_chart hc hBc
  obtain ⟨hVi, hVfr⟩ := hV.isPLBall_image_chart hc hVc
  have hSc : S ⊆ c.source := hBV.symm.subset.trans (inter_subset_left.trans hBc)
  obtain ⟨q, hq, -⟩ := hS.exists_isPLHomeomorphOn_image_chart hc hSc
  have hmeet : c '' B ∩ c '' V = c '' S := by
    rw [← hBV]
    exact (c.injOn.image_inter hBc hVc).symm
  have hSV' : c '' S ⊆ frontier (c '' V) := by
    rw [← hVfr, hV.boundary_eq_frontier]
    exact image_mono hSV
  have hi := isPLBall_union_of_inter_eq_of_subset_frontier hBi hVi ⟨q, hq⟩ hmeet hSV'
  rw [← image_union] at hi
  have hic : c '' (B ∪ V) ⊆ c.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (union_subset hBc hVc hx)
  have h := hi.isPLCellOn_frontier.image_chart_symm hc hic
  have heq : c.symm '' (c '' (B ∪ V)) = B ∪ V :=
    c.symm_image_image_of_subset_source (union_subset hBc hVc)
  rw [heq] at h
  rwa [h.boundary_eq_frontier] at h

theorem IsPLCellOn.union_biUnion_range_of_attach_in_chart {B BB : Set M}
    (hB : IsPLCellOn 3 B BB) {W WBd S SBd : ℕ → Set M} (k : ℕ)
    (hW : ∀ i < k, IsPLCellOn 3 (W (i + 1)) (WBd (i + 1)))
    (hS : ∀ i < k, IsPLCellOn 2 (S i) (SBd i))
    (hSW : ∀ i < k, S i ⊆ frontier (W (i + 1)))
    (hmeet : ∀ i < k, (B ∪ ⋃ j ∈ Finset.range i, W (j + 1)) ∩ W (i + 1) = S i)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hBc : B ⊆ c.source)
    (hWc : ∀ i < k, W (i + 1) ⊆ c.source) :
    IsPLCellOn 3 (B ∪ ⋃ j ∈ Finset.range k, W (j + 1))
      (frontier (B ∪ ⋃ j ∈ Finset.range k, W (j + 1))) := by
  induction k with
  | zero =>
    have hB' : IsPLCellOn 3 B (frontier B) := hB.boundary_eq_frontier ▸ hB
    simpa using hB'
  | succ k ih =>
    have h := ih (fun i hi => hW i (by omega)) (fun i hi => hS i (by omega))
      (fun i hi => hSW i (by omega)) (fun i hi => hmeet i (by omega))
      (fun i hi => hWc i (by omega))
    have hsub : (B ∪ ⋃ j ∈ Finset.range k, W (j + 1)) ⊆ c.source :=
      union_subset hBc (iUnion₂_subset fun j hj => hWc j (by
        have := Finset.mem_range.mp hj
        omega))
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm (W (k + 1)), ← union_assoc]
    exact h.union_of_inter_eq_of_subset_frontier_in_chart (hW k (by omega))
      (hS k (by omega)) (hmeet k (by omega)) (hSW k (by omega)) hc hsub (hWc k (by omega))

end DifferentialGeometry.Topology.PiecewiseLinear
