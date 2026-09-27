/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellFaceOrderOfInteriors
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCellRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualFlagBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualInteriorSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSource

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compactDualCutCell_flag_incidence
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space) :
    (∀ l, compactDualCutBoundary M K hKM l =
      ⋃ m ∈ section34Face (compactDualCutCell M K hKM) l \ {l},
        compactDualCutCell M K hKM m) ∧
    (∀ l m, compactDualCutCell M K hKM l ∩ compactDualCutCell M K hKM m =
      ⋃ k ∈ section34Face (compactDualCutCell M K hKM) l ∩
        section34Face (compactDualCutCell M K hKM) m, compactDualCutCell M K hKM k) ∧
    ∀ l m, compactDualCutCell M K hKM m ⊆ compactDualCutCell M K hKM l →
      m = l ∨ section34BoundedDim m < section34BoundedDim l := by
  have hbd := compactDualCutBoundary_eq_iUnion_step M K hKM hM hK hint
  have hcell := isPLCellOn_compactDualCutCell M K hKM hM hK hint
  have hstep (m l : Section34CompactLabelOf K K) (h : Section34CompactCutStep m l) :
      compactDualCutCell M K hKM m ⊆ compactDualCutBoundary M K hKM l := by
    rw [hbd l]
    exact subset_iUnion₂_of_subset m h subset_rfl
  exact boundary_inter_and_strict_of_disjoint_interiors section34CompactCutStep_dim_lt hstep
    (fun l => (hbd l).subset) (fun l => (hcell l).boundary_subset)
    (fun l => (hcell l).sdiff_boundary_nonempty)
    (compactDualCutCell_inter_subset_boundaries M K hM hK hKM hint hstep)

end DifferentialGeometry.Topology.PiecewiseLinear
