/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskArcGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PLArcChainUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  {c : OpenPartialHomeomorph M E3}

theorem IsPLCellOn.union_of_inter_eq_arc_in_chart {D₁ B₁ D₂ B₂ A Ab : Set M}
    (hD₁ : IsPLCellOn 2 D₁ B₁) (hD₂ : IsPLCellOn 2 D₂ B₂) (hA : IsPLCellOn 1 A Ab)
    (hinter : D₁ ∩ D₂ = A) (hAB₁ : A ⊆ B₁) (hAB₂ : A ⊆ B₂)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hD₁c : D₁ ⊆ c.source)
    (hD₂c : D₂ ⊆ c.source) :
    IsPLCellOn 2 (D₁ ∪ D₂) ((B₁ ∪ B₂) \ (A \ Ab)) := by
  have hAc : A ⊆ c.source := (hinter.symm.subset.trans inter_subset_left).trans hD₁c
  have hB₁c := hD₁.boundary_subset.trans hD₁c
  have hB₂c := hD₂.boundary_subset.trans hD₂c
  have hBc := union_subset hB₁c hB₂c
  obtain ⟨q₁, hq₁, hb₁⟩ := hD₁.exists_isPLHomeomorphOn_image_chart hc hD₁c
  obtain ⟨q₂, hq₂, hb₂⟩ := hD₂.exists_isPLHomeomorphOn_image_chart hc hD₂c
  obtain ⟨r, hr, hrb⟩ := hA.exists_isPLHomeomorphOn_image_chart hc hAc
  have hAi : IsPLCellOn 1 (c '' A) (c '' Ab) := by
    rw [hrb]
    exact isPLCellOn_id_of_isPLBall hr
  obtain ⟨γ, hγ, hγb⟩ := hAi.exists_isPLHomeomorphOn_Icc
  have hinteri : c '' D₁ ∩ c '' D₂ = c '' A := by
    rw [← c.injOn.image_inter hD₁c hD₂c, hinter]
  obtain ⟨q, hq, hqb⟩ := exists_isPLHomeomorphOn_union_of_inter_eq_arc hq₁ hq₂ hγ hinteri
    (hb₁ ▸ image_mono hAB₁) (hb₂ ▸ image_mono hAB₂)
  have hbound : q '' stdSimplexBoundary 2 = c '' ((B₁ ∪ B₂) \ (A \ Ab)) := by
    rw [hqb, ← hb₁, ← hb₂, ← hγb,
      (c.injOn.mono hBc).image_sdiff_subset (sdiff_subset.trans (hAB₁.trans subset_union_left)),
      image_union, (c.injOn.mono hAc).image_sdiff_subset hA.boundary_subset]
  rw [← image_union] at hq
  have hct : c '' (D₁ ∪ D₂) ⊆ c.target :=
    image_subset_iff.mpr fun z hz => c.map_source (union_subset hD₁c hD₂c hz)
  have hi := (isPLCellOn_id_of_isPLBall hq).image_chart_symm hc hct
  have hpull : c.symm '' (c '' (D₁ ∪ D₂)) = D₁ ∪ D₂ :=
    c.symm_image_image_of_subset_source (union_subset hD₁c hD₂c)
  have hbpull : c.symm '' (c '' ((B₁ ∪ B₂) \ (A \ Ab))) = (B₁ ∪ B₂) \ (A \ Ab) :=
    c.symm_image_image_of_subset_source (sdiff_subset.trans hBc)
  rwa [hpull, hbound, hbpull] at hi

end DifferentialGeometry.Topology.PiecewiseLinear
