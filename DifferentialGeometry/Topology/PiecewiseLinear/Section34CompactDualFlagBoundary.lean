/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundedLabelUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualArcBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualOuterBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualPatchBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSplitBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compactDualCutBoundary_markedPoint_eq_empty
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (p : Section34CompactMarkIndex K K) :
    compactDualCutBoundary M K hKM (.markedPoint p) = ∅ := by
  obtain ⟨P, r, u, -, -, -, hbd⟩ := isPLCellOn_compactDualMarkedPoint M K hKM p
  rw [hbd, stdSimplexBoundary_zero, image_empty, image_empty]

theorem compactDualCutBoundary_eq_iUnion_step
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space)
    (l : Section34CompactLabelOf K K) :
    compactDualCutBoundary M K hKM l =
      ⋃ (m : Section34CompactLabelOf K K) (_ : Section34CompactCutStep m l),
        compactDualCutCell M K hKM m := by
  rw [iUnion_section34BoundedLabel]
  cases l with
  | vertexBall w =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_vertexBall_eq_union M K hM hK hKM hint w
  | tetraBall t =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_tetraBall_eq_union M K hKM hM t
  | splitDisk e =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_splitDisk_eq_union M K hM hK hKM hint e
  | faceDisk s =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_faceDisk_eq_iUnion_faceArc M K hKM s
  | patch x =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_patch_eq_union M K hKM x
  | faceArc a =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_faceArc_eq_iUnion_markedPoint M K hKM a
  | edgeArc i =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_edgeArc_eq_iUnion_markedPoint M K hKM i
  | markedPoint p =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_markedPoint_eq_empty M K hKM p
  | outerFace o =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_outerFace_eq_union M K hM hK hKM hint o
  | outerArc q =>
    simpa only [Section34CompactCutStep, iUnion_false, iUnion_empty, empty_union, union_empty]
      using compactDualCutBoundary_outerArc_eq_union M K hM hK hKM hint q

end DifferentialGeometry.Topology.PiecewiseLinear
