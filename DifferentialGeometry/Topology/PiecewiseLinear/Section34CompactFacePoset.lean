/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSplitDiskIntersection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem Section34CompactCutStep.dim_succ
    {K K' : Geometry.SimplicialComplex ℝ E3}
    {m l : Section34CompactLabelOf K K'} (h : Section34CompactCutStep m l) :
    section34BoundedDim l = section34BoundedDim m + 1 := by
  cases m <;> cases l <;> simp_all [Section34CompactCutStep, section34BoundedDim]

section Frame

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem Section34CompactCutFrame.srcBd_subset_src
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (l : Section34CompactLabelOf K K') : srcBd l ⊆ src l := by
  obtain ⟨_, _, _, _, _, _, hcell, _⟩ := hcut
  exact (hcell l).boundary_subset

theorem Section34CompactCutFrame.srcBd_eq_frontier_of_dim_three
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {l : Section34CompactLabelOf K K'} (hl : section34BoundedDim l = 3) :
    srcBd l = frontier (src l) := by
  obtain ⟨_, _, _, _, _, _, hcell, _⟩ := hcut
  have h3 : IsPLCellOn 3 (src l) (srcBd l) := by simpa only [hl] using hcell l
  exact h3.boundary_eq_frontier

theorem Section34CompactCutFrame.eq_of_src_eq
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {l m : Section34CompactLabelOf K K'} (h : src l = src m) : l = m := by
  have hcut' := hcut
  obtain ⟨_, _, _, _, _, _, hcell, _⟩ := hcut
  have hm : IsPLCellOn (section34BoundedDim m) (src l) (srcBd m) := h ▸ hcell m
  have hdim : section34BoundedDim l = section34BoundedDim m := (hcell l).dim_eq hm
  exact hcut'.eq_of_subset_of_dim_le (by rw [h]) (le_of_eq hdim.symm)

end Frame

end DifferentialGeometry.Topology.PiecewiseLinear
