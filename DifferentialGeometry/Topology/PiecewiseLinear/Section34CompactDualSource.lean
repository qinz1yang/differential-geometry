/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCellSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem section34CompactCutStep_dim_lt
    {K K' : Geometry.SimplicialComplex ℝ E3} (m l : Section34CompactLabelOf K K')
    (h : Section34CompactCutStep m l) : section34BoundedDim m < section34BoundedDim l := by
  cases m <;> cases l <;> simp_all only [Section34CompactCutStep, section34BoundedDim] <;>
    omega

theorem compactVertexIndex_subset_vertexBall
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (w : Section34CompactVertexIndex K K) :
    (w.1 : Set E3) ⊆ compactDualVertexBall M K w := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  have hvL : {w.1.centroid ℝ id} ∈ L.faces := by
    rw [singleton_centroid_eq_compactVertexIndex w]
    exact ⟨w.2.1, w.2.2.2⟩
  have hv := mem_graphDualCell_space_of_singleton_mem M L
    ((restrict_faces_subset K _).trans hKM) hvL
  rw [← singleton_centroid_eq_compactVertexIndex w, Finset.coe_singleton,
    singleton_subset_iff]
  exact hv

theorem compactDualVertexBall_inter_convexHull_eq_empty
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (w : Section34CompactVertexIndex K K) {s : Finset E3} (hs : s ∈ K.faces)
    (hws : ¬ Section34Incident w.1 s) :
    compactDualVertexBall M K w ∩ convexHull ℝ (s : Set E3) = ∅ := by
  classical
  apply graphDualCell_space_inter_convexHull_eq_empty _
    (hKM (centroid_mem_vertices_compactVertexIndex w)) (hKM hs)
  intro hw
  apply hws
  rw [Section34Incident, ← singleton_centroid_eq_compactVertexIndex w,
    Finset.coe_singleton, singleton_subset_iff]
  exact subset_convexHull ℝ _ hw

theorem compactDualSplitDisk_inter_convexHull_eq_empty
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (e : Section34CompactEdgeIndex K K) {s : Finset E3} (hs : s ∈ K.faces)
    (hes : ¬ Section34Incident e.1 s) :
    compactDualSplitDisk M K hKM e ∩ convexHull ℝ (s : Set E3) = ∅ := by
  classical
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hxe, hxs⟩
  have hsub := subset_of_mem_dualCell_of_mem_convexHull M (hKM e.2.1) (hKM hs)
    (splittingDisk_space_subset_dualCell M (hKM e.2.1) hxe) hxs
  exact hes ((Finset.coe_subset.mpr hsub).trans (subset_convexHull ℝ _))

theorem compactDualVertexBall_splitDisk_incidence
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (w : Section34CompactVertexIndex K K) (e : Section34CompactEdgeIndex K K)
    (h : (compactDualVertexBall M K w ∩ compactDualSplitDisk M K hKM e).Nonempty) :
    w.1 ⊆ e.1 :=
  compact_vertex_split_incidence hKM w e
    (singleton_centroid_eq_compactVertexIndex w).symm h

theorem compactDualSplitDisk_eq_inter_vertexBalls
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (e : Section34CompactEdgeIndex K K) :
    ∃ w w' : Section34CompactVertexIndex K K, w ≠ w' ∧
      (e.1 : Set E3) = (w.1 : Set E3) ∪ (w'.1 : Set E3) ∧
      compactDualSplitDisk M K hKM e =
        compactDualVertexBall M K w ∩ compactDualVertexBall M K w' := by
  classical
  obtain ⟨u, v, huv, he⟩ := Finset.card_eq_two.mp e.2.2.1
  have hue : u ∈ e.1 := by rw [he]; simp
  have hve : v ∈ e.1 := by rw [he]; simp
  have huK : {u} ∈ K.faces := K.down_closed e.2.1
    (Finset.singleton_subset_iff.mpr hue) (Finset.singleton_nonempty u)
  have hvK : {v} ∈ K.faces := K.down_closed e.2.1
    (Finset.singleton_subset_iff.mpr hve) (Finset.singleton_nonempty v)
  let w : Section34CompactVertexIndex K K := ⟨{u}, huK, by simp,
    convexHull_subset_section34CompactGraphSkeleton huK (by simp)⟩
  let w' : Section34CompactVertexIndex K K := ⟨{v}, hvK, by simp,
    convexHull_subset_section34CompactGraphSkeleton hvK (by simp)⟩
  refine ⟨w, w', ?_, ?_, ?_⟩
  · intro h
    have hval := congrArg Subtype.val h
    exact huv (Finset.singleton_injective hval)
  · simp only [w, w', he, Finset.coe_insert, Finset.coe_singleton, singleton_union]
  · let L := restrict K (section34CompactGraphSkeleton K)
    have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
    have hEq := graphDualCell_space_inter_of_mem M L hLM
      (fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs)
      (show e.1 ∈ L.faces from ⟨e.2.1, e.2.2.2⟩) hue hve huv
    simpa only [compactDualVertexBall, compactDualSplitDisk, w, w',
      Finset.centroid_singleton, id_eq] using hEq.symm

theorem compactDualCutCell_subset_top_cell
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (l : Section34CompactLabelOf K K) :
    ∃ m : Section34CompactLabelOf K K, section34BoundedDim m = 3 ∧
      compactDualCutCell M K hKM l ⊆ compactDualCutCell M K hKM m := by
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  have hE (e : Section34CompactEdgeIndex K K) :
      ∃ w : Section34CompactVertexIndex K K,
        compactDualSplitDisk M K hKM e ⊆ compactDualVertexBall M K w := by
    obtain ⟨w, w', -, -, hEq⟩ := compactDualSplitDisk_eq_inter_vertexBalls M K hKM e
    exact ⟨w, hEq.subset.trans inter_subset_left⟩
  cases l with
  | vertexBall w => exact ⟨.vertexBall w, rfl, subset_rfl⟩
  | tetraBall t => exact ⟨.tetraBall t, rfl, subset_rfl⟩
  | splitDisk e =>
    obtain ⟨w, hw⟩ := hE e
    exact ⟨.vertexBall w, rfl, hw⟩
  | faceDisk s =>
    obtain ⟨t, ht, hst, htc⟩ := hK.exists_face_superset_card_eq s.2.1
    let t' : Section34CompactSimplexIndex K 4 := ⟨t, ht, htc⟩
    refine ⟨.tetraBall t', rfl, ?_⟩
    exact compact_face_disk_subset_residual_ball s t'
      ((Finset.coe_subset.mpr hst).trans (subset_convexHull ℝ _))
  | patch x => exact ⟨.tetraBall x.1.1, rfl, inter_subset_left⟩
  | faceArc a => exact ⟨.vertexBall a.1.2, rfl, inter_subset_left⟩
  | edgeArc i => exact ⟨.tetraBall i.1.1, rfl, inter_subset_left⟩
  | markedPoint p =>
    obtain ⟨w, hw⟩ := hE p.1.2
    exact ⟨.vertexBall w, rfl, inter_subset_left.trans hw⟩
  | outerFace o =>
    have hc := isClosed_compactDualVertexBall M K o.1
    exact ⟨.vertexBall o.1, rfl, closure_minimal (sdiff_subset.trans hc.frontier_subset) hc⟩
  | outerArc q =>
    obtain ⟨w, hw⟩ := hE q.1
    refine ⟨.vertexBall w, rfl, Subset.trans ?_ hw⟩
    exact closure_minimal (sdiff_subset.trans (boundaryComplex_space_subset 2 _))
      (isClosed_compactDualSplitDisk M K hKM q.1)

end DifferentialGeometry.Topology.PiecewiseLinear
