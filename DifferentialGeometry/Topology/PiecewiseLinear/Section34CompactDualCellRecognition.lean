/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchRecognition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLCellOn_compactDualCutCell
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space)
    (l : Section34CompactLabelOf K K) :
    IsPLCellOn (section34BoundedDim l) (compactDualCutCell M K hKM l)
      (compactDualCutBoundary M K hKM l) := by
  cases l with
  | vertexBall w => exact isPLCellOn_compactDualVertexBall M K hKM hM w
  | tetraBall t => exact isPLCellOn_compactDualTetraBall M K hKM t
  | splitDisk e => exact isPLCellOn_compactDualSplitDisk M K hKM hM e
  | faceDisk s => exact isPLCellOn_compactDualFaceDisk M K hKM s
  | patch x =>
    exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.patch x)
      (isPLBall_compactDualCutCell_patch M K hKM x)
  | faceArc a => exact isPLCellOn_compactDualFaceArc M K hKM a
  | edgeArc i => exact isPLCellOn_compactDualEdgeArc M K hKM i
  | markedPoint p => exact isPLCellOn_compactDualMarkedPoint M K hKM p
  | outerFace o =>
    exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.outerFace o)
      (isPLBall_compactDualCutCell_outerFace M K hM hK hKM hint o)
  | outerArc q =>
    exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.outerArc q)
      (isPLBall_compactDualCutCell_outerArc M K hM hK hKM hint q)

end DifferentialGeometry.Topology.PiecewiseLinear
