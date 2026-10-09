/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTopInteriors
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterRecognition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualVertexBall_inter_subset_splitDisks
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (w v : Section34CompactVertexIndex K K) (hwv : w ≠ v) :
    compactDualVertexBall M K w ∩ compactDualVertexBall M K v ⊆
      ⋃ e : Section34CompactEdgeIndex K K, compactDualSplitDisk M K hKM e := by
  let : DecidableEq E3 := Classical.decEq E3
  let L := restrict K (section34CompactGraphSkeleton K)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 :=
    fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs
  have hvertex (p : Section34CompactVertexIndex K K) : {p.1.centroid ℝ id} ∈ L.faces := by
    rw [singleton_centroid_eq_compactVertexIndex p]
    exact ⟨p.2.1, p.2.2.2⟩
  have hne : w.1.centroid ℝ id ≠ v.1.centroid ℝ id := by
    intro h
    apply hwv
    apply Subtype.ext
    rw [← singleton_centroid_eq_compactVertexIndex w,
      ← singleton_centroid_eq_compactVertexIndex v, h]
  intro x hx
  by_cases he : {w.1.centroid ℝ id, v.1.centroid ℝ id} ∈ L.faces
  · let e : Section34CompactEdgeIndex K K :=
      ⟨{w.1.centroid ℝ id, v.1.centroid ℝ id}, he.1, Finset.card_pair hne, he.2⟩
    refine mem_iUnion.mpr ⟨e, ?_⟩
    change x ∈ (splittingDisk M {w.1.centroid ℝ id, v.1.centroid ℝ id} (hLM he)).space
    rw [← graphDualCell_space_inter M L hLM hcard hne he]
    exact hx
  · have hzero := graphDualCell_space_inter_eq_empty M L hLM hcard
      (hvertex w) (hvertex v) hne he
    exact ((eq_empty_iff_forall_notMem.mp hzero) x hx).elim

open Classical in
theorem disjoint_compactDualSplitDisk (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces) (e f : Section34CompactEdgeIndex K K) (hef : e ≠ f) :
    Disjoint (compactDualSplitDisk M K hKM e) (compactDualSplitDisk M K hKM f) :=
  disjoint_splittingDisk_space M (hKM e.2.1) (hKM f.2.1)
    (fun h => hef (Subtype.ext h)) (by rw [e.2.2.1, f.2.2.1])

open Classical in
theorem compactDualOuterArc_subset_splitBoundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutCell M K hKM (.outerArc q) ⊆
      compactDualCutBoundary M K hKM (.splitDisk q.1) := by
  let D := splittingDisk M q.1.1 (hKM q.1.2.1)
  let _ : Finite D.faces := (splittingDisk_faces_finite M (hKM q.1.2.1)).to_subtype
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  rw [compactDualCutBoundary_splitDisk M K hKM q.1]
  exact closure_minimal sdiff_subset (isPolyhedron_space (boundaryComplex 2 D)).isClosed

open Classical in
theorem compactDualOuterFace_inter_cell_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K)
    (l : Section34CompactLabelOf K K) (hl : section34BoundedDim l ≤ 2)
    (hne : .outerFace o ≠ l) :
    compactDualCutCell M K hKM (.outerFace o) ∩ compactDualCutCell M K hKM l ⊆
      compactDualCutBoundary M K hKM (.outerFace o) := by
  rw [compactDualCutBoundary_outerFace_eq_inter M K hM hK hKM hint o]
  intro x hx
  refine ⟨hx.1, ?_⟩
  cases l with
  | vertexBall w => simp [section34BoundedDim] at hl
  | tetraBall t => simp [section34BoundedDim] at hl
  | splitDisk e => exact Or.inr (mem_iUnion.mpr ⟨e, hx.2⟩)
  | faceDisk s => exact Or.inl (compactDualResidualCell_subset_space M K s.2.1 hx.2)
  | patch p => exact Or.inl (compactDualResidualCell_subset_space M K p.1.1.2.1 hx.2.1)
  | faceArc a => exact Or.inl (compactDualResidualCell_subset_space M K a.1.1.2.1 hx.2.2)
  | edgeArc i => exact Or.inl (compactDualResidualCell_subset_space M K i.1.1.2.1 hx.2.1)
  | markedPoint p => exact Or.inl (compactDualResidualCell_subset_space M K p.1.1.2.1 hx.2.2)
  | outerFace p =>
    have hop : o.1 ≠ p.1 := fun h => hne
      (congrArg Section34BoundedLabel.outerFace (Subtype.ext h))
    exact Or.inr (compactDualVertexBall_inter_subset_splitDisks M K hKM o.1 p.1 hop
      ⟨compactDualOuterFace_subset_vertexBall M K hKM o hx.1,
        compactDualOuterFace_subset_vertexBall M K hKM p hx.2⟩)
  | outerArc q =>
    exact Or.inr (mem_iUnion.mpr ⟨q.1, compactDualOuterArc_subset_splitDisk M K hKM q hx.2⟩)

open Classical in
theorem compactDualOuterArc_inter_cell_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K)
    (l : Section34CompactLabelOf K K) (hl : section34BoundedDim l ≤ 2)
    (hne : .outerArc q ≠ l) :
    compactDualCutCell M K hKM (.outerArc q) ∩ compactDualCutCell M K hKM l ⊆
      compactDualCutBoundary M K hKM (.outerArc q) ∪ compactDualCutBoundary M K hKM l := by
  have hbase := compactDualCutCell_outerArc_inter_base_subset_boundary M K hM hK hKM hint q
  intro x hx
  cases l with
  | vertexBall w => simp [section34BoundedDim] at hl
  | tetraBall t => simp [section34BoundedDim] at hl
  | splitDisk e =>
    by_cases hqe : q.1 = e
    · subst e
      exact Or.inr (compactDualOuterArc_subset_splitBoundary M K hKM q hx.1)
    · exact (Set.disjoint_left.mp (disjoint_compactDualSplitDisk M K hKM q.1 e hqe)
        (compactDualOuterArc_subset_splitDisk M K hKM q hx.1) hx.2).elim
  | faceDisk s =>
    exact Or.inl (hbase ⟨hx.1, compactDualResidualCell_subset_space M K s.2.1 hx.2⟩)
  | patch p =>
    exact Or.inl (hbase ⟨hx.1, compactDualResidualCell_subset_space M K p.1.1.2.1 hx.2.1⟩)
  | faceArc a =>
    exact Or.inl (hbase ⟨hx.1, compactDualResidualCell_subset_space M K a.1.1.2.1 hx.2.2⟩)
  | edgeArc i =>
    exact Or.inl (hbase ⟨hx.1, compactDualResidualCell_subset_space M K i.1.1.2.1 hx.2.1⟩)
  | markedPoint p =>
    exact Or.inl (hbase ⟨hx.1, compactDualResidualCell_subset_space M K p.1.1.2.1 hx.2.2⟩)
  | outerFace o =>
    exact Or.inr (compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o
      (.outerArc q) (by simp [section34BoundedDim]) (by simp) ⟨hx.2, hx.1⟩)
  | outerArc r =>
    have hqr : q.1 ≠ r.1 := fun h => hne
      (congrArg Section34BoundedLabel.outerArc (Subtype.ext h))
    exact (Set.disjoint_left.mp (disjoint_compactDualSplitDisk M K hKM q.1 r.1 hqr)
      (compactDualOuterArc_subset_splitDisk M K hKM q hx.1)
      (compactDualOuterArc_subset_splitDisk M K hKM r hx.2)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
