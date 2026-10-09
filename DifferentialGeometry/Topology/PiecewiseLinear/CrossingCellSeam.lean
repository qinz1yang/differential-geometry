/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingCellInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellIntersectionBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasPLCurveCrossingOnAt.not_subset_of_cell_seam_in_chart
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {A B Ab Bb Db J : Set M} (hA : IsPLCellOn 3 A Ab) (hB : IsPLCellOn 3 B Bb)
    (hD : IsPLCellOn 2 (A ∩ B) Db) {x : M} (c : OpenPartialHomeomorph M E3)
    (hxc : x ∈ c.source)
    (hc : HasPLCurveCrossingOnAt (c '' (frontier (A ∪ B) ∩ c.source))
      (c '' (J ∩ c.source)) (c '' (Db ∩ c.source)) (c x)) : ¬ J ⊆ A := by
  intro hJA
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hBc : IsClosed B := hB.isCompact.isClosed
  have hDB : A ∩ B ⊆ Bb := by
    rw [inter_comm]
    exact hB.inter_subset_boundary_of_isPLCellOn hA (inter_comm A B ▸ hD)
  obtain ⟨hQ, hDQ⟩ := hB.isPLCellOn_closure_boundary_sdiff hD hDB
  let Q := closure (Bb \ (A ∩ B))
  have hQS : Q ⊆ frontier (A ∪ B) := by
    apply closure_minimal _ isClosed_frontier
    rintro y ⟨hyB, hyD⟩
    have hyF : y ∈ frontier B := hB.boundary_eq_frontier ▸ hyB
    have hyA : y ∈ Aᶜ := fun hy => hyD ⟨hy, hBc.frontier_subset hyF⟩
    have heq : (A ∪ B) ∩ Aᶜ = B ∩ Aᶜ := by
      ext z
      simp only [mem_inter_iff, mem_union, mem_compl_iff]
      tauto
    have hfr : frontier (A ∪ B) ∩ Aᶜ = frontier B ∩ Aᶜ := by
      rw [← frontier_inter_open_inter hAc.isOpen_compl, heq,
        frontier_inter_open_inter hAc.isOpen_compl]
    exact (hfr.symm.subset ⟨hyF, hyA⟩).1
  have hQA : Disjoint (Q \ Db) A := by
    apply Set.disjoint_left.mpr
    rintro y ⟨hyQ, hyDb⟩ hyA
    have hQB : Q ⊆ B := closure_minimal
      (sdiff_subset.trans hB.boundary_subset) hBc
    exact hyDb (hDQ.subset ⟨⟨hyA, hQB hyQ⟩, hyQ⟩)
  have hcl := HasPLCurveCrossingOnAt.mem_closure_inter_cellInterior_in_chart
    c hxc hc hQ hQS (Filter.Eventually.of_forall fun _ => Iff.rfl)
  change x ∈ closure (J ∩ (Q \ Db)) at hcl
  have hempty : J ∩ (Q \ Db) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyJ, hyQ⟩
    exact Set.disjoint_left.mp hQA hyQ (hJA hyJ)
  simp only [hempty, closure_empty, mem_empty_iff_false] at hcl

end DifferentialGeometry.Topology.PiecewiseLinear
