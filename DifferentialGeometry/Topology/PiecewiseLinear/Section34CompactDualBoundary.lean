/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCells
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSubcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_vertexBall (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (w : Section34CompactVertexIndex K K) :
    compactDualCutBoundary M K hKM (.vertexBall w) =
      (boundaryComplex 3 (graphDualCell M (restrict K (section34CompactGraphSkeleton K))
        (w.1.centroid ℝ id))).space := by
  classical
  change (boundaryComplex 3 (restrict (secondDerived M)
    (graphDualCell M (restrict K (section34CompactGraphSkeleton K))
      (w.1.centroid ℝ id)).space)).space = _
  let L := restrict K (section34CompactGraphSkeleton K)
  let G := graphDualCell M L (w.1.centroid ℝ id)
  have hGRc : G.faces ⊆ (@secondDerived E3 _ _ (Classical.decEq E3) M).faces :=
    (graphDualCell_faces_subset M L (w.1.centroid ℝ id)).trans
      (@derivedNeighborhood_faces_subset E3 _ _ (Classical.decEq E3) M L)
  have hR : @secondDerived E3 _ _ (Classical.decEq E3) M = secondDerived M :=
    congrArg (fun d : DecidableEq E3 => @secondDerived E3 _ _ d M)
      (Subsingleton.elim _ _)
  have hGR : G.faces ⊆ (secondDerived M).faces := hR ▸ hGRc
  have hEq : restrict (secondDerived M) G.space = G :=
    restrict_eq_of_subcomplex (secondDerived M) G hGR
  exact congrArg (fun A : Geometry.SimplicialComplex ℝ E3 => (boundaryComplex 3 A).space) hEq

open Classical in
theorem compactDualCutBoundary_splitDisk (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (e : Section34CompactEdgeIndex K K) :
    compactDualCutBoundary M K hKM (.splitDisk e) =
      (boundaryComplex 2 (splittingDisk M e.1 (hKM e.2.1))).space := by
  classical
  change (boundaryComplex 2 (restrict (secondDerived M)
    (splittingDisk M e.1 (hKM e.2.1)).space)).space = _
  let G := splittingDisk M e.1 (hKM e.2.1)
  have hGRc : G.faces ⊆ (@secondDerived E3 _ _ (Classical.decEq E3) M).faces :=
    splittingDisk_faces_subset M (hKM e.2.1)
  have hR : @secondDerived E3 _ _ (Classical.decEq E3) M = secondDerived M :=
    congrArg (fun d : DecidableEq E3 => @secondDerived E3 _ _ d M)
      (Subsingleton.elim _ _)
  have hGR : G.faces ⊆ (secondDerived M).faces := hR ▸ hGRc
  have hEq : restrict (secondDerived M) G.space = G :=
    restrict_eq_of_subcomplex (secondDerived M) G hGR
  exact congrArg (fun A : Geometry.SimplicialComplex ℝ E3 => (boundaryComplex 2 A).space) hEq

theorem isPLCellOn_compactDualVertexBall (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (w : Section34CompactVertexIndex K K) :
    IsPLCellOn 3 (compactDualVertexBall M K w)
      (compactDualCutBoundary M K hKM (.vertexBall w)) := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  let G := graphDualCell M L (w.1.centroid ℝ id)
  let _ : Finite G.faces := (graphDualCell_faces_finite M L _).to_subtype
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hwL : {w.1.centroid ℝ id} ∈ L.faces := by
    rw [singleton_centroid_eq_compactVertexIndex w]
    exact ⟨w.2.1, w.2.2.2⟩
  have hball : IsPLBall 3 G.space := hM.isPLBall_graphDualCell M L hLM
    (fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs) hwL
  obtain ⟨r, hr⟩ := hball
  have hcell := isPLCellOn_id_of_isPLBall hr
  rw [hr.image_stdSimplexBoundary_eq_boundaryComplex G rfl] at hcell
  rw [compactDualCutBoundary_vertexBall M K hKM w]
  exact hcell

theorem isPLCellOn_compactDualSplitDisk (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (e : Section34CompactEdgeIndex K K) :
    IsPLCellOn 2 (compactDualSplitDisk M K hKM e)
      (compactDualCutBoundary M K hKM (.splitDisk e)) := by
  classical
  let G := splittingDisk M e.1 (hKM e.2.1)
  let _ : Finite G.faces := (splittingDisk_faces_finite M (hKM e.2.1)).to_subtype
  have hball : IsPLBall 2 G.space :=
    hM.isPLBall_splittingDisk M (hKM e.2.1) (k := 1) e.2.2.1 (by decide)
  obtain ⟨r, hr⟩ := hball
  have hcell := isPLCellOn_id_of_isPLBall hr
  rw [hr.image_stdSimplexBoundary_eq_boundaryComplex G rfl] at hcell
  rw [compactDualCutBoundary_splitDisk M K hKM e]
  exact hcell

theorem compactDualCutBoundary_vertexBall_eq_frontier
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (w : Section34CompactVertexIndex K K) :
    compactDualCutBoundary M K hKM (.vertexBall w) =
      frontier (compactDualVertexBall M K w) :=
  (isPLCellOn_compactDualVertexBall M K hKM hM w).boundary_eq_frontier

theorem compactDualCutCell_outerFace (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (o : Section34CompactOuterVertexIndex K K) :
    compactDualCutCell M K hKM (.outerFace o) =
      closure (compactDualCutBoundary M K hKM (.vertexBall o.1) \
        (K.space ∪ ⋃ e : Section34CompactEdgeIndex K K,
          compactDualCutCell M K hKM (.splitDisk e))) := by
  rw [compactDualCutBoundary_vertexBall_eq_frontier M K hKM hM o.1]
  rfl

theorem compactDualCutCell_outerArc (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutCell M K hKM (.outerArc q) =
      closure (compactDualCutBoundary M K hKM (.splitDisk q.1) \ K.space) := by
  rw [compactDualCutBoundary_splitDisk M K hKM q.1]
  rfl

end DifferentialGeometry.Topology.PiecewiseLinear
