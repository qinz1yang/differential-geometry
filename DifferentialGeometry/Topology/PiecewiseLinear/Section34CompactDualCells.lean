/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
noncomputable def compactDualVertexBall (M K : Geometry.SimplicialComplex ℝ E3)
    (w : Section34CompactVertexIndex K K) : Set E3 :=
  (graphDualCell M (restrict K (section34CompactGraphSkeleton K))
    (w.1.centroid ℝ id)).space

open Classical in
noncomputable def compactDualSplitDisk (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (e : Section34CompactEdgeIndex K K) : Set E3 :=
  (splittingDisk M e.1 (hKM e.2.1)).space

open Classical in
noncomputable def compactDualNeighborhood (M K : Geometry.SimplicialComplex ℝ E3) : Set E3 :=
  ⋃ v ∈ K.vertices, (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space

noncomputable def compactDualResidualCell (M K : Geometry.SimplicialComplex ℝ E3)
    (s : Finset E3) : Set E3 :=
  closure (convexHull ℝ (s : Set E3) \ compactDualNeighborhood M K)

open Classical in
noncomputable def compactDualCutCell (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) : Section34CompactLabelOf K K → Set E3
  | .vertexBall w => compactDualVertexBall M K w
  | .tetraBall t => compactDualResidualCell M K t.1
  | .splitDisk e => compactDualSplitDisk M K hKM e
  | .faceDisk s => compactDualResidualCell M K s.1
  | .patch x => compactDualResidualCell M K x.1.1.1 ∩ compactDualVertexBall M K x.1.2
  | .faceArc a => compactDualVertexBall M K a.1.2 ∩ compactDualResidualCell M K a.1.1.1
  | .edgeArc i => compactDualResidualCell M K i.1.1.1 ∩ compactDualSplitDisk M K hKM i.1.2
  | .markedPoint p => compactDualSplitDisk M K hKM p.1.2 ∩
      compactDualResidualCell M K p.1.1.1
  | .outerFace o => closure (frontier (compactDualVertexBall M K o.1) \
      (K.space ∪ ⋃ e : Section34CompactEdgeIndex K K, compactDualSplitDisk M K hKM e))
  | .outerArc q => closure
      ((boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space \ K.space)

open Classical in
noncomputable def compactDualCutBoundary (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (l : Section34CompactLabelOf K K) : Set E3 :=
  (boundaryComplex (section34BoundedDim l)
    (restrict (secondDerived M) (compactDualCutCell M K hKM l))).space

theorem singleton_centroid_eq_compactVertexIndex
    {K : Geometry.SimplicialComplex ℝ E3} (w : Section34CompactVertexIndex K K) :
    {w.1.centroid ℝ id} = w.1 := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  simp only [hv, Finset.centroid_singleton, id_eq]

theorem centroid_mem_vertices_compactVertexIndex
    {K : Geometry.SimplicialComplex ℝ E3} (w : Section34CompactVertexIndex K K) :
    w.1.centroid ℝ id ∈ K.vertices := by
  change {w.1.centroid ℝ id} ∈ K.faces
  rw [singleton_centroid_eq_compactVertexIndex w]
  exact w.2.1

theorem iUnion_compactDualVertexBall (M K : Geometry.SimplicialComplex ℝ E3) :
    (⋃ w : Section34CompactVertexIndex K K, compactDualVertexBall M K w) =
      compactDualNeighborhood M K := by
  classical
  apply Subset.antisymm
  · refine iUnion_subset fun w => ?_
    exact subset_iUnion₂_of_subset (w.1.centroid ℝ id)
      (centroid_mem_vertices_compactVertexIndex w) subset_rfl
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    let w : Section34CompactVertexIndex K K := ⟨{v}, hv, Finset.card_singleton v,
      convexHull_subset_section34CompactGraphSkeleton hv (by simp)⟩
    refine mem_iUnion.mpr ⟨w, ?_⟩
    simpa only [compactDualVertexBall, w, Finset.centroid_singleton, id_eq] using hxv

theorem compactDualNeighborhood_eq_cutNeighborhood
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces) :
    compactDualNeighborhood M K =
      section34CompactCutNeighborhood (compactDualCutCell M K hKM) :=
  (iUnion_compactDualVertexBall M K).symm

theorem compactDualVertexBall_subset_neighborhood (M K : Geometry.SimplicialComplex ℝ E3)
    (w : Section34CompactVertexIndex K K) :
    compactDualVertexBall M K w ⊆ compactDualNeighborhood M K := by
  rw [← iUnion_compactDualVertexBall M K]
  exact subset_iUnion (fun w => compactDualVertexBall M K w) w

theorem compactDualSplitDisk_subset_neighborhood (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (e : Section34CompactEdgeIndex K K) :
    compactDualSplitDisk M K hKM e ⊆ compactDualNeighborhood M K := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have heL : e.1 ∈ L.faces := ⟨e.2.1, e.2.2.2⟩
  obtain ⟨u, hu⟩ := K.nonempty_of_mem_faces e.2.1
  have hcard : 1 < e.1.card := by rw [e.2.2.1]; omega
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne hcard u
  have huK : u ∈ K.vertices := K.down_closed e.2.1
    (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty u)
  have hinter := graphDualCell_space_inter_of_mem M L hLM
    (fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs)
    heL hu hv hvu.symm
  change (splittingDisk M e.1 (hKM e.2.1)).space ⊆ compactDualNeighborhood M K
  rw [← hinter]
  exact inter_subset_left.trans (subset_iUnion₂_of_subset u huK subset_rfl)

theorem compactDualResidualCell_subset_space (M K : Geometry.SimplicialComplex ℝ E3)
    {s : Finset E3} (hs : s ∈ K.faces) : compactDualResidualCell M K s ⊆ K.space :=
  (closure_minimal sdiff_subset (s.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
    (K.convexHull_subset_space hs)

theorem isClosed_compactDualVertexBall (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (w : Section34CompactVertexIndex K K) :
    IsClosed (compactDualVertexBall M K w) := by
  let _ : Finite (graphDualCell M (restrict K (section34CompactGraphSkeleton K))
      (w.1.centroid ℝ id)).faces := (graphDualCell_faces_finite M _ _).to_subtype
  exact (SimplicialComplex.isCompact_geometricSpace _).isClosed

theorem isClosed_compactDualSplitDisk (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (hKM : K.faces ⊆ M.faces) (e : Section34CompactEdgeIndex K K) :
    IsClosed (compactDualSplitDisk M K hKM e) := by
  let _ : Finite (splittingDisk M e.1 (hKM e.2.1)).faces :=
    (splittingDisk_faces_finite M (hKM e.2.1)).to_subtype
  exact (SimplicialComplex.isCompact_geometricSpace _).isClosed

theorem compactDualCutCell_subset_space_union (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (hKM : K.faces ⊆ M.faces) (l : Section34CompactLabelOf K K) :
    compactDualCutCell M K hKM l ⊆ K.space ∪ compactDualNeighborhood M K := by
  cases l with
  | vertexBall w =>
    exact (compactDualVertexBall_subset_neighborhood M K w).trans subset_union_right
  | tetraBall t =>
    exact (compactDualResidualCell_subset_space M K t.2.1).trans subset_union_left
  | splitDisk e =>
    exact (compactDualSplitDisk_subset_neighborhood M K hKM e).trans subset_union_right
  | faceDisk s =>
    exact (compactDualResidualCell_subset_space M K s.2.1).trans subset_union_left
  | patch x =>
    exact inter_subset_left.trans
      ((compactDualResidualCell_subset_space M K x.1.1.2.1).trans subset_union_left)
  | faceArc a =>
    exact inter_subset_right.trans
      ((compactDualResidualCell_subset_space M K a.1.1.2.1).trans subset_union_left)
  | edgeArc i =>
    exact inter_subset_left.trans
      ((compactDualResidualCell_subset_space M K i.1.1.2.1).trans subset_union_left)
  | markedPoint p =>
    exact inter_subset_right.trans
      ((compactDualResidualCell_subset_space M K p.1.1.2.1).trans subset_union_left)
  | outerFace o =>
    have hclosed := isClosed_compactDualVertexBall M K o.1
    exact (closure_minimal (sdiff_subset.trans hclosed.frontier_subset) hclosed).trans
      ((compactDualVertexBall_subset_neighborhood M K o.1).trans subset_union_right)
  | outerArc q =>
    have hclosed := isClosed_compactDualSplitDisk M K hKM q.1
    have hbd : (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space ⊆
        compactDualSplitDisk M K hKM q.1 :=
      space_mono_of_faces_subset (boundaryComplex_faces_subset 2 _)
    exact (closure_minimal (sdiff_subset.trans hbd) hclosed).trans
      ((compactDualSplitDisk_subset_neighborhood M K hKM q.1).trans subset_union_right)

theorem iUnion_compactDualCutCell (M K : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    (⋃ l : Section34CompactLabelOf K K, compactDualCutCell M K hKM l) =
      K.space ∪ compactDualNeighborhood M K := by
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  apply Subset.antisymm
  · exact iUnion_subset fun l => compactDualCutCell_subset_space_union M K hKM l
  · rw [← compact_cut_primary_cover (fun _ hs => hK.exists_face_superset_card_eq hs)
      (compactDualNeighborhood M K)]
    refine union_subset ?_ (iUnion_subset fun t => ?_)
    · rw [← iUnion_compactDualVertexBall M K]
      exact iUnion_subset fun w => subset_iUnion_of_subset (.vertexBall w) subset_rfl
    · exact subset_iUnion_of_subset (.tetraBall t) subset_rfl

theorem compactDualCutCell_faceArc (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (a : Section34CompactArcIndex K K) :
    compactDualCutCell M K hKM (.faceArc a) =
      compactDualCutCell M K hKM (.vertexBall a.1.2) ∩
        compactDualCutCell M K hKM (.faceDisk a.1.1) := rfl

theorem compactDualCutCell_markedPoint (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (p : Section34CompactMarkIndex K K) :
    compactDualCutCell M K hKM (.markedPoint p) =
      compactDualCutCell M K hKM (.splitDisk p.1.2) ∩
        compactDualCutCell M K hKM (.faceDisk p.1.1) := rfl

theorem compactDualCutCell_patch (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (x : Section34CompactPatchIndex K K) :
    compactDualCutCell M K hKM (.patch x) =
      compactDualCutCell M K hKM (.tetraBall x.1.1) ∩
        compactDualCutCell M K hKM (.vertexBall x.1.2) := rfl

theorem compactDualCutCell_edgeArc (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (i : Section34CompactEdgeArcIndex K K) :
    compactDualCutCell M K hKM (.edgeArc i) =
      compactDualCutCell M K hKM (.tetraBall i.1.1) ∩
        compactDualCutCell M K hKM (.splitDisk i.1.2) := rfl

theorem compactDualCutCell_faceDisk (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    compactDualCutCell M K hKM (.faceDisk s) = closure (convexHull ℝ (s.1 : Set E3) \
      section34CompactCutNeighborhood (compactDualCutCell M K hKM)) := by
  rw [← compactDualNeighborhood_eq_cutNeighborhood M K hKM]
  rfl

theorem compactDualCutCell_tetraBall (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (t : Section34CompactSimplexIndex K 4) :
    compactDualCutCell M K hKM (.tetraBall t) = closure (convexHull ℝ (t.1 : Set E3) \
      section34CompactCutNeighborhood (compactDualCutCell M K hKM)) := by
  rw [← compactDualNeighborhood_eq_cutNeighborhood M K hKM]
  rfl

end DifferentialGeometry.Topology.PiecewiseLinear
