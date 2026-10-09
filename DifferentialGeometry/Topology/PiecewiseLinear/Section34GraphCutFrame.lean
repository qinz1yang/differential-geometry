/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutCellRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphVertexBoundaryCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphTetrahedronBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphFaceBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphArcBoundaries
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphSplitBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphPatchBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeBoundaries

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem section34GraphCutFamily_isCutFrame
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hU : IsOpen U) (hK : IsCombinatorialManifold 3 𝒦.complex)
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) :
    Section34CutFrame U 𝒦 𝒦' (section34GraphCutFamily 𝒦 𝒦')
      (fun l => ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') l \ {l},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  refine ⟨hK, hsub, hmap, ?_, fun _ => rfl,
    section34GraphCutFamily_inter_eq_iUnion_common_faces hsub hmap,
    section34GraphCutFamily_subset_eq_or_dim_lt hU hsub hmap hK',
    section34GraphCutFamily_source_clauses hsub hmap hK.isCombinatorialManifoldWithBoundary⟩
  intro l
  cases l with
  | vertexBall w =>
      have hV := isPLCellOn_section34GraphVertexCell hsub hmap
        hK'.isCombinatorialManifoldWithBoundary w
      rwa [section34GraphVertexBoundary_eq_iUnion_proper_faces hU hsub hmap
        hK.isCombinatorialManifoldWithBoundary hK'] at hV
  | tetraBall t =>
      exact isPLCellOn_section34GraphResidualTetrahedron_proper_faces hU hsub hmap
        hK.isCombinatorialManifoldWithBoundary hK' t
  | splitDisk e =>
      exact isPLCellOn_section34GraphSplitCell_proper_faces hsub hmap
        hK.isCombinatorialManifoldWithBoundary hK' e
  | faceDisk s => exact isPLCellOn_section34GraphResidualTriangle_proper_faces hsub hmap s
  | patch p => exact isPLCellOn_section34GraphPatch_proper_faces hsub hmap hK' p
  | faceArc a => exact isPLCellOn_section34GraphFaceArc_proper_faces hsub hmap hK' a
  | edgeArc i =>
      exact isPLCellOn_section34GraphEdgeArc_proper_faces hsub hmap
        hK.isCombinatorialManifoldWithBoundary hK' i
  | markedPoint p => exact isPLCellOn_section34GraphMarkedPoint_proper_faces hsub hmap hK' p

end DifferentialGeometry.Topology.PiecewiseLinear
