/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCellInteriors

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compactDualOuterFace_subset_vertexBall
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (o : Section34CompactOuterVertexIndex K K) :
    compactDualCutCell M K hKM (.outerFace o) ⊆ compactDualVertexBall M K o.1 := by
  have hclosed := isClosed_compactDualVertexBall M K o.1
  exact closure_minimal (sdiff_subset.trans hclosed.frontier_subset) hclosed

theorem compactDualOuterArc_subset_splitDisk
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutCell M K hKM (.outerArc q) ⊆ compactDualSplitDisk M K hKM q.1 := by
  exact closure_minimal (sdiff_subset.trans
    (space_mono_of_faces_subset (boundaryComplex_faces_subset 2 _)))
    (isClosed_compactDualSplitDisk M K hKM q.1)

theorem compactDualSplitDisk_inter_vertex_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (w : Section34CompactVertexIndex K K) (e : Section34CompactEdgeIndex K K) :
    compactDualVertexBall M K w ∩ compactDualSplitDisk M K hKM e ⊆
      compactDualCutBoundary M K hKM (.vertexBall w) := by
  classical
  let v := w.1.centroid ℝ id
  let L := restrict K (section34CompactGraphSkeleton K)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 :=
    fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs
  have hvM : {v} ∈ M.faces := hKM (centroid_mem_vertices_compactVertexIndex w)
  have heL : e.1 ∈ L.faces := ⟨e.2.1, e.2.2.2⟩
  rw [compactDualCutBoundary_vertexBall_eq_frontier M K hKM hM w]
  rintro x ⟨hxV, hxD⟩
  have hve : v ∈ e.1 := mem_of_graphDualCell_inter_splittingDisk_nonempty M L hvM
    (hKM e.2.1) ⟨x, hxV, hxD⟩
  have hc : 1 < e.1.card := by rw [e.2.2.1]; omega
  obtain ⟨u, hue, huv⟩ := Finset.exists_mem_ne hc v
  have huK : {u} ∈ K.faces := K.down_closed e.2.1
    (Finset.singleton_subset_iff.mpr hue) (Finset.singleton_nonempty u)
  have huL : {u} ∈ L.faces :=
    ⟨huK, convexHull_subset_section34CompactGraphSkeleton huK (by simp)⟩
  have hEq := graphDualCell_space_inter_of_mem M L hLM hcard heL hve hue huv.symm
  have hI : IsPLBall 2 ((graphDualCell M L v).space ∩ (graphDualCell M L u).space) := by
    rw [hEq]
    exact hM.isPLBall_splittingDisk M (hLM heL) (k := 1) e.2.2.1 (by decide)
  have hbd := (hM.isPLBall_graphDualCell M L hLM hcard huL).inter_subset_frontier_of_isPLBall
    hI (by decide)
  have hxI : x ∈ (graphDualCell M L v).space ∩ (graphDualCell M L u).space := by
    rw [hEq]
    exact hxD
  exact hbd hxI

theorem compactDualVertexBall_inter_cell_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (w : Section34CompactVertexIndex K K) (l : Section34CompactLabelOf K K)
    (hne : .vertexBall w ≠ l) :
    compactDualVertexBall M K w ∩ compactDualCutCell M K hKM l ⊆
      compactDualCutBoundary M K hKM (.vertexBall w) := by
  classical
  cases l with
  | vertexBall v =>
    exact compactDualVertexBall_inter_subset_boundary M K hKM hM w v
      (fun h => hne (congrArg Section34BoundedLabel.vertexBall h))
  | tetraBall t => exact compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w t.1
  | splitDisk e => exact compactDualSplitDisk_inter_vertex_subset_boundary M K hKM hM w e
  | faceDisk s => exact compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w s.1
  | patch p =>
    intro x hx
    exact compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w p.1.1.1
      ⟨hx.1, hx.2.1⟩
  | faceArc a =>
    intro x hx
    exact compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w a.1.1.1
      ⟨hx.1, hx.2.2⟩
  | edgeArc i =>
    intro x hx
    exact compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w i.1.1.1
      ⟨hx.1, hx.2.1⟩
  | markedPoint p =>
    intro x hx
    exact compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w p.1.1.1
      ⟨hx.1, hx.2.2⟩
  | outerFace o =>
    intro x hx
    by_cases hwo : w = o.1
    · subst w
      rw [compactDualCutBoundary_vertexBall_eq_frontier M K hKM hM o.1]
      exact closure_minimal sdiff_subset isClosed_frontier hx.2
    · exact compactDualVertexBall_inter_subset_boundary M K hKM hM w o.1 hwo
        ⟨hx.1, compactDualOuterFace_subset_vertexBall M K hKM o hx.2⟩
  | outerArc q =>
    intro x hx
    exact compactDualSplitDisk_inter_vertex_subset_boundary M K hKM hM w q.1
      ⟨hx.1, compactDualOuterArc_subset_splitDisk M K hKM q hx.2⟩

theorem compactDualTetraBall_inter_faceDisk_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (t : Section34CompactSimplexIndex K 4)
    (s : Section34CompactSimplexIndex K 3) :
    compactDualResidualCell M K t.1 ∩ compactDualResidualCell M K s.1 ⊆
      compactDualCutBoundary M K hKM (.tetraBall t) := by
  classical
  rw [(isPLCellOn_compactDualTetraBall M K hKM t).boundary_eq_frontier]
  have hsub (u : Finset E3) :
      compactDualResidualCell M K u ⊆ convexHull ℝ (u : Set E3) :=
    closure_minimal sdiff_subset (u.finite_toSet.isCompact_convexHull ℝ).isClosed
  rintro x ⟨hxt, hxs⟩
  refine ⟨subset_closure hxt, fun hxint => ?_⟩
  have hxopen : x ∈ openSimplex t.1 := by
    rw [← interior_convexHull_eq_openSimplex (K.indep t.2.1)
      (by rw [t.2.2, finrank_euclideanSpace_fin])]
    exact interior_mono (hsub t.1) hxint
  have hts := face_subset_of_mem_openSimplex_of_mem_convexHull K t.2.1 s.2.1 hxopen
    (hsub s.1 hxs)
  have hcard := Finset.card_le_card hts
  rw [t.2.2, s.2.2] at hcard
  omega

theorem compactDualTetraBall_inter_cell_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (t : Section34CompactSimplexIndex K 4) (l : Section34CompactLabelOf K K)
    (hne : .tetraBall t ≠ l) :
    compactDualResidualCell M K t.1 ∩ compactDualCutCell M K hKM l ⊆
      compactDualCutBoundary M K hKM (.tetraBall t) := by
  have hN := compactDualResidualCell_inter_neighborhood_subset_boundary M K hKM hM t
  cases l with
  | vertexBall w =>
    exact (inter_subset_inter_right _ (compactDualVertexBall_subset_neighborhood M K w)).trans hN
  | tetraBall u =>
    exact compactDualResidualCell_inter_subset_boundary M K hKM t u
      (fun h => hne (congrArg Section34BoundedLabel.tetraBall h))
  | splitDisk e =>
    exact (inter_subset_inter_right _
      (compactDualSplitDisk_subset_neighborhood M K hKM e)).trans hN
  | faceDisk s => exact compactDualTetraBall_inter_faceDisk_subset_boundary M K hKM t s
  | patch p =>
    intro x hx
    exact hN ⟨hx.1, compactDualVertexBall_subset_neighborhood M K p.1.2 hx.2.2⟩
  | faceArc a =>
    intro x hx
    exact compactDualTetraBall_inter_faceDisk_subset_boundary M K hKM t a.1.1
      ⟨hx.1, hx.2.2⟩
  | edgeArc i =>
    intro x hx
    exact hN ⟨hx.1, compactDualSplitDisk_subset_neighborhood M K hKM i.1.2 hx.2.2⟩
  | markedPoint p =>
    intro x hx
    exact hN ⟨hx.1, compactDualSplitDisk_subset_neighborhood M K hKM p.1.2 hx.2.1⟩
  | outerFace o =>
    intro x hx
    exact hN ⟨hx.1, compactDualVertexBall_subset_neighborhood M K o.1
      (compactDualOuterFace_subset_vertexBall M K hKM o hx.2)⟩
  | outerArc q =>
    intro x hx
    exact hN ⟨hx.1, compactDualSplitDisk_subset_neighborhood M K hKM q.1
      (compactDualOuterArc_subset_splitDisk M K hKM q hx.2)⟩

theorem compactDualCutCell_inter_subset_boundary_of_left_dim_eq_three
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (l m : Section34CompactLabelOf K K) (hl : section34BoundedDim l = 3) (hlm : l ≠ m) :
    compactDualCutCell M K hKM l ∩ compactDualCutCell M K hKM m ⊆
      compactDualCutBoundary M K hKM l := by
  rcases section34BoundedDim_eq_three hl with ⟨w, rfl⟩ | ⟨t, rfl⟩
  · exact compactDualVertexBall_inter_cell_subset_boundary M K hKM hM w m hlm
  · exact compactDualTetraBall_inter_cell_subset_boundary M K hKM hM t m hlm

end DifferentialGeometry.Topology.PiecewiseLinear
