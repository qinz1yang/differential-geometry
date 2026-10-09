/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraceInteriors

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem compact_inter_boundary_symm {A B Ab Bb : Set E3}
    (h : B ∩ A ⊆ Bb ∪ Ab) : A ∩ B ⊆ Ab ∪ Bb :=
  fun _ hx => (h ⟨hx.2, hx.1⟩).symm

open Classical in
theorem compactDualCutCell_inter_subset_boundaries
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (l m : Section34CompactLabelOf K K) (hne : l ≠ m) :
    compactDualCutCell M K hKM l ∩ compactDualCutCell M K hKM m ⊆
      compactDualCutBoundary M K hKM l ∪ compactDualCutBoundary M K hKM m := by
  classical
  cases l with
  | vertexBall w =>
    exact (compactDualVertexBall_inter_cell_subset_boundary M K hKM hM w m hne).trans
      subset_union_left
  | tetraBall t =>
    exact (compactDualTetraBall_inter_cell_subset_boundary M K hKM hM t m hne).trans
      subset_union_left
  | faceDisk s =>
    by_cases hm : section34BoundedDim m = 3
    · exact compact_inter_boundary_symm
        ((compactDualCutCell_inter_subset_boundary_of_left_dim_eq_three M K hKM hM m
          (.faceDisk s) hm hne.symm).trans
        subset_union_left)
    · have hm2 : section34BoundedDim m ≤ 2 := by
        have hle := section34BoundedDim_le_three m
        omega
      exact (compactDualFaceDisk_inter_cell_subset_boundary M K hKM s m hm2 hne).trans
        subset_union_left
  | splitDisk e =>
    by_cases hm : section34BoundedDim m = 3
    · exact compact_inter_boundary_symm
        ((compactDualCutCell_inter_subset_boundary_of_left_dim_eq_three M K hKM hM m
          (.splitDisk e) hm hne.symm).trans
        subset_union_left)
    · have hm2 : section34BoundedDim m ≤ 2 := by
        have hle := section34BoundedDim_le_three m
        omega
      exact compactDualSplitDisk_inter_cell_subset_boundary M K hM hK hKM hint e m hm2 hne
  | outerFace o =>
    by_cases hm : section34BoundedDim m = 3
    · exact compact_inter_boundary_symm
        ((compactDualCutCell_inter_subset_boundary_of_left_dim_eq_three M K hKM hM m
          (.outerFace o) hm hne.symm).trans
        subset_union_left)
    · have hm2 : section34BoundedDim m ≤ 2 := by
        have hle := section34BoundedDim_le_three m
        omega
      exact (compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o m hm2 hne).trans
        subset_union_left
  | outerArc q =>
    by_cases hm : section34BoundedDim m = 3
    · exact compact_inter_boundary_symm
        ((compactDualCutCell_inter_subset_boundary_of_left_dim_eq_three M K hKM hM m
          (.outerArc q) hm hne.symm).trans
        subset_union_left)
    · have hm2 : section34BoundedDim m ≤ 2 := by
        have hle := section34BoundedDim_le_three m
        omega
      exact compactDualOuterArc_inter_cell_subset_boundary M K hM hK hKM hint q m hm2 hne
  | patch p =>
    cases m with
    | vertexBall w =>
      exact compact_inter_boundary_symm
        ((compactDualVertexBall_inter_cell_subset_boundary M K hKM hM w
        (.patch p) hne.symm).trans
        subset_union_left)
    | tetraBall t =>
      exact compact_inter_boundary_symm
        ((compactDualTetraBall_inter_cell_subset_boundary M K hKM hM t
        (.patch p) hne.symm).trans
        subset_union_left)
    | faceDisk s =>
      exact compact_inter_boundary_symm
        ((compactDualFaceDisk_inter_cell_subset_boundary M K hKM s
        (.patch p) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | splitDisk e =>
      exact compact_inter_boundary_symm
        (compactDualSplitDisk_inter_cell_subset_boundary M K hM hK hKM hint e
        (.patch p) (by simp [section34BoundedDim]) hne.symm)
    | outerFace o =>
      exact compact_inter_boundary_symm
        ((compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o
        (.patch p) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | outerArc r =>
      exact compact_inter_boundary_symm
        (compactDualOuterArc_inter_cell_subset_boundary M K hM hK hKM hint r
        (.patch p) (by simp [section34BoundedDim]) hne.symm)
    | patch p' =>
      exact compactDualPatch_inter_patch_subset_boundary M K hKM hstep p p'
        (fun h => hne (congrArg Section34BoundedLabel.patch h))
    | faceArc a =>
      exact compactDualPatch_inter_faceArc_subset_boundary M K hKM hstep p a
    | edgeArc i =>
      exact compactDualPatch_inter_edgeArc_subset_boundary M K hKM hstep p i
    | markedPoint q =>
      exact compactDualPatch_inter_markedPoint_subset_boundary M K hKM hstep p q
  | faceArc a =>
    cases m with
    | vertexBall w =>
      exact compact_inter_boundary_symm
        ((compactDualVertexBall_inter_cell_subset_boundary M K hKM hM w
        (.faceArc a) hne.symm).trans
        subset_union_left)
    | tetraBall t =>
      exact compact_inter_boundary_symm
        ((compactDualTetraBall_inter_cell_subset_boundary M K hKM hM t
        (.faceArc a) hne.symm).trans
        subset_union_left)
    | faceDisk s =>
      exact compact_inter_boundary_symm
        ((compactDualFaceDisk_inter_cell_subset_boundary M K hKM s
        (.faceArc a) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | splitDisk e =>
      exact compact_inter_boundary_symm
        (compactDualSplitDisk_inter_cell_subset_boundary M K hM hK hKM hint e
        (.faceArc a) (by simp [section34BoundedDim]) hne.symm)
    | outerFace o =>
      exact compact_inter_boundary_symm
        ((compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o
        (.faceArc a) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | outerArc r =>
      exact compact_inter_boundary_symm
        (compactDualOuterArc_inter_cell_subset_boundary M K hM hK hKM hint r
        (.faceArc a) (by simp [section34BoundedDim]) hne.symm)
    | patch p =>
      exact compact_inter_boundary_symm
        (compactDualPatch_inter_faceArc_subset_boundary M K hKM hstep p a)
    | faceArc a' =>
      exact compactDualFaceArc_inter_faceArc_subset_boundary M K hKM hstep a a'
        (fun h => hne (congrArg Section34BoundedLabel.faceArc h))
    | edgeArc i =>
      exact compactDualFaceArc_inter_edgeArc_subset_boundary M K hKM hstep a i
    | markedPoint q =>
      exact compactDualFaceArc_inter_markedPoint_subset_boundary M K hKM hstep a q
  | edgeArc i =>
    cases m with
    | vertexBall w =>
      exact compact_inter_boundary_symm
        ((compactDualVertexBall_inter_cell_subset_boundary M K hKM hM w
        (.edgeArc i) hne.symm).trans
        subset_union_left)
    | tetraBall t =>
      exact compact_inter_boundary_symm
        ((compactDualTetraBall_inter_cell_subset_boundary M K hKM hM t
        (.edgeArc i) hne.symm).trans
        subset_union_left)
    | faceDisk s =>
      exact compact_inter_boundary_symm
        ((compactDualFaceDisk_inter_cell_subset_boundary M K hKM s
        (.edgeArc i) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | splitDisk e =>
      exact compact_inter_boundary_symm
        (compactDualSplitDisk_inter_cell_subset_boundary M K hM hK hKM hint e
        (.edgeArc i) (by simp [section34BoundedDim]) hne.symm)
    | outerFace o =>
      exact compact_inter_boundary_symm
        ((compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o
        (.edgeArc i) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | outerArc r =>
      exact compact_inter_boundary_symm
        (compactDualOuterArc_inter_cell_subset_boundary M K hM hK hKM hint r
        (.edgeArc i) (by simp [section34BoundedDim]) hne.symm)
    | patch p =>
      exact compact_inter_boundary_symm
        (compactDualPatch_inter_edgeArc_subset_boundary M K hKM hstep p i)
    | faceArc a =>
      exact compact_inter_boundary_symm
        (compactDualFaceArc_inter_edgeArc_subset_boundary M K hKM hstep a i)
    | edgeArc i' =>
      exact compactDualEdgeArc_inter_edgeArc_subset_boundary M K hKM hstep i i'
        (fun h => hne (congrArg Section34BoundedLabel.edgeArc h))
    | markedPoint q =>
      exact compactDualEdgeArc_inter_markedPoint_subset_boundary M K hKM hstep i q
  | markedPoint q =>
    cases m with
    | vertexBall w =>
      exact compact_inter_boundary_symm
        ((compactDualVertexBall_inter_cell_subset_boundary M K hKM hM w
        (.markedPoint q) hne.symm).trans
        subset_union_left)
    | tetraBall t =>
      exact compact_inter_boundary_symm
        ((compactDualTetraBall_inter_cell_subset_boundary M K hKM hM t
        (.markedPoint q) hne.symm).trans
        subset_union_left)
    | faceDisk s =>
      exact compact_inter_boundary_symm
        ((compactDualFaceDisk_inter_cell_subset_boundary M K hKM s
        (.markedPoint q) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | splitDisk e =>
      exact compact_inter_boundary_symm
        (compactDualSplitDisk_inter_cell_subset_boundary M K hM hK hKM hint e
        (.markedPoint q) (by simp [section34BoundedDim]) hne.symm)
    | outerFace o =>
      exact compact_inter_boundary_symm
        ((compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o
        (.markedPoint q) (by simp [section34BoundedDim]) hne.symm).trans
        subset_union_left)
    | outerArc r =>
      exact compact_inter_boundary_symm
        (compactDualOuterArc_inter_cell_subset_boundary M K hM hK hKM hint r
        (.markedPoint q) (by simp [section34BoundedDim]) hne.symm)
    | patch p =>
      exact compact_inter_boundary_symm
        (compactDualPatch_inter_markedPoint_subset_boundary M K hKM hstep p q)
    | faceArc a =>
      exact compact_inter_boundary_symm
        (compactDualFaceArc_inter_markedPoint_subset_boundary M K hKM hstep a q)
    | edgeArc i =>
      exact compact_inter_boundary_symm
        (compactDualEdgeArc_inter_markedPoint_subset_boundary M K hKM hstep i q)
    | markedPoint q' =>
      exact compactDualMarkedPoint_inter_markedPoint_subset_boundary M K hKM q q'
        (fun h => hne (congrArg Section34BoundedLabel.markedPoint h))

end DifferentialGeometry.Topology.PiecewiseLinear
