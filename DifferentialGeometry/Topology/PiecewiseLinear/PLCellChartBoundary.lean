/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellChartGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.boundary_subset_frontier_union_in_chart {B₁ B₁b B₂ B₂b E Eb : Set M}
    (hE : IsPLCellOn 2 E Eb) (hB₁ : IsPLCellOn 3 B₁ B₁b) (hB₂ : IsPLCellOn 3 B₂ B₂b)
    (hEq : B₁ ∩ B₂ = E) (hEfr : E ⊆ frontier B₁)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hB₁c : B₁ ⊆ c.source) (hB₂c : B₂ ⊆ c.source) :
    Eb ⊆ frontier (B₁ ∪ B₂) := by
  have hEc : E ⊆ c.source := hEq.symm.subset.trans (inter_subset_left.trans hB₁c)
  obtain ⟨hB₁i, hB₁fr⟩ := hB₁.isPLBall_image_chart hc hB₁c
  obtain ⟨hB₂i, -⟩ := hB₂.isPLBall_image_chart hc hB₂c
  obtain ⟨q, hq, hqb⟩ := hE.exists_isPLHomeomorphOn_image_chart hc hEc
  have hEi : IsPLCellOn 2 (c '' E) (c '' Eb) := by
    rw [hqb]
    exact isPLCellOn_id_of_isPLBall hq
  have hEqi : c '' B₁ ∩ c '' B₂ = c '' E := by
    rw [← hEq]
    exact (c.injOn.image_inter hB₁c hB₂c).symm
  have hEfri : c '' E ⊆ frontier (c '' B₁) := by
    rw [← hB₁fr, hB₁.boundary_eq_frontier]
    exact image_mono hEfr
  have hW' := hB₂.union_of_inter_eq_of_subset_frontier_in_chart hB₁ hE
    (by rw [inter_comm, hEq]) hEfr hc hB₂c hB₁c
  have hW : IsPLCellOn 3 (B₁ ∪ B₂) (frontier (B₁ ∪ B₂)) := by
    simpa only [union_comm B₂ B₁] using hW'
  have hWfr := (hW.isPLBall_image_chart hc (union_subset hB₁c hB₂c)).2
  intro y hy
  have hcy := boundary_subset_frontier_union_of_inter_eq hB₁i hB₂i hEi hEqi hEfri
    (mem_image_of_mem c hy)
  rw [← image_union, ← hWfr] at hcy
  obtain ⟨x, hx, hxy⟩ := hcy
  have hxy' : x = y := c.injOn
    (union_subset hB₁c hB₂c (hW.isCompact.isClosed.frontier_subset hx))
    (hEc (hE.boundary_subset hy)) hxy
  exact hxy' ▸ hx

end DifferentialGeometry.Topology.PiecewiseLinear
