/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualFlags
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkCondition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem section34CompactCutFrame_compactDual
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space) :
    Section34CompactCutFrame K.space K K (compactDualCutCell M K hKM)
      (compactDualCutBoundary M K hKM) := by
  have hfin : K.faces.Finite := (Set.toFinite M.faces).subset hKM
  let _ : Finite K.faces := hfin.to_subtype
  have hcell := isPLCellOn_compactDualCutCell M K hKM hM hK hint
  obtain ⟨hbd, hinter, hdim⟩ := compactDualCutCell_flag_incidence M K hKM hM hK hint
  have hres (s : Finset E3) :
      compactDualResidualCell M K s ⊆ convexHull ℝ (s : Set E3) :=
    closure_minimal sdiff_subset (s.finite_toSet.isCompact_convexHull ℝ).isClosed
  have havoidV (s : Finset E3) (hs : s ∈ K.faces) (w : Section34CompactVertexIndex K K)
      (hws : ¬ Section34Incident w.1 s) :
      compactDualResidualCell M K s ∩ compactDualVertexBall M K w = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxR, hxV⟩
    exact (eq_empty_iff_forall_notMem.mp
      (compactDualVertexBall_inter_convexHull_eq_empty M K hKM w hs hws)) x
      ⟨hxV, hres s hxR⟩
  have havoidE (s : Finset E3) (hs : s ∈ K.faces) (e : Section34CompactEdgeIndex K K)
      (hes : ¬ Section34Incident e.1 s) :
      compactDualResidualCell M K s ∩ compactDualSplitDisk M K hKM e = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxR, hxE⟩
    exact (eq_empty_iff_forall_notMem.mp
      (compactDualSplitDisk_inter_convexHull_eq_empty M K hKM e hs hes)) x
      ⟨hxE, hres s hxR⟩
  refine ⟨rfl, hfin, hfin, hK, IsSubdivision.refl K,
    IsCombinatorialManifoldWithBoundary.section34CompactLinkCondition hfin hK,
    hcell, hbd, hinter, hdim, ?_, compactDualCutCell_faceArc M K hKM,
    compactDualCutCell_markedPoint M K hKM, compactDualCutCell_patch M K hKM,
    compactDualCutCell_edgeArc M K hKM, compactDualCutCell_outerFace M K hKM hM,
    compactDualCutCell_outerArc M K hKM, compactDualCutCell_faceDisk M K hKM,
    compactDualCutCell_tetraBall M K hKM,
    (fun s w h => havoidV s.1 s.2.1 w h), (fun s e h => havoidE s.1 s.2.1 e h),
    (fun t w h => havoidV t.1 t.2.1 w h), (fun t e h => havoidE t.1 t.2.1 e h),
    compactDualCutCell_subset_top_cell M K hKM hK,
    compactVertexIndex_subset_vertexBall M K hKM,
    compactDualVertexBall_splitDisk_incidence M K hKM,
    compactDualSplitDisk_eq_inter_vertexBalls M K hKM,
    (fun t s h => compact_face_disk_subset_residual_ball s t h), ?_⟩
  · rw [← compactDualNeighborhood_eq_cutNeighborhood M K hKM]
    exact iUnion_compactDualCutCell M K hKM hK
  · intro s
    obtain ⟨t, ht, hst, htc⟩ := hK.exists_face_superset_card_eq s.2.1
    exact ⟨⟨t, ht, htc⟩, (Finset.coe_subset.mpr hst).trans (subset_convexHull ℝ _)⟩

theorem IsPLBall.exists_compactDualCutFrame {C V : Set E3}
    (hC : IsPLBall 3 C) (hV : IsOpen V) (hCV : C ⊆ V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces),
      M.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 M ∧ M.space ⊆ V ∧
      C ⊆ interior M.space ∧ K.space = C ∧
      (∀ s ∈ M.faces, Metric.diam (convexHull ℝ (s : Set E3)) < δ) ∧
      Section34CompactCutFrame C K K (compactDualCutCell M K hKM)
        (compactDualCutBoundary M K hKM) := by
  obtain ⟨M, hMfin, hM, hMV, hint, hKC, hmesh⟩ :=
    hC.exists_collarTriangulation hV hCV hδ
  let _ : Finite M.faces := hMfin.to_subtype
  let K := restrict M C
  have hKM : K.faces ⊆ M.faces := restrict_faces_subset M C
  let _ : Finite K.faces := (hMfin.subset hKM).to_subtype
  have hKB : IsPLBall 3 K.space := hKC.symm ▸ hC
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    hKB.isCombinatorialManifoldWithBoundary
  refine ⟨M, K, hKM, hMfin, hM, hMV, hint, hKC, hmesh, ?_⟩
  have hcut := section34CompactCutFrame_compactDual M K hKM hM hK (hKC.symm ▸ hint)
  have hKC' : K.space = C := hKC
  exact hKC' ▸ hcut

end DifferentialGeometry.Topology.PiecewiseLinear
