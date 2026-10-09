/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualOuterSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_splitDisk_eq_inter_frontier
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (e : Section34CompactEdgeIndex K K) :
    compactDualCutBoundary M K hKM (.splitDisk e) =
      compactDualSplitDisk M K hKM e ∩ frontier (compactDualNeighborhood M K) := by
  let L := restrict K (section34CompactGraphSkeleton K)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have heL : e.1 ∈ L.faces := ⟨e.2.1, e.2.2.2⟩
  have hLi : ∀ v ∈ L.vertices, v ∈ interior M.space := by
    intro v hv
    exact hint (K.convexHull_subset_space hv.1 (subset_convexHull ℝ _
      (Finset.mem_singleton_self v)))
  obtain ⟨r, hr, hrim⟩ :=
    hM.exists_isPLHomeomorphOn_splittingDisk_inter_frontier (n := 2) (k := 1)
      (show Module.finrank ℝ E3 = 2 + 1 from finrank_euclideanSpace_fin)
      hLM hLi heL e.2.2.1 (by decide) (fun s hs => by
        rw [e.2.2.1]
        exact card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs)
  have hlocal : IsPLCellOn 2 (compactDualSplitDisk M K hKM e)
      (r '' stdSimplexBoundary 2) := isPLCellOn_id_of_isPLBall hr
  have hbd := (isPLCellOn_compactDualSplitDisk M K hKM hM e).boundary_eq hlocal
  have hverts : L.vertices = K.vertices :=
    vertices_eq_setOf_restrict_section34CompactGraphSkeleton.symm
  rw [hbd]
  rw [hverts] at hrim
  exact hrim.symm

open Classical in
theorem compactDualSplitDisk_inter_residual_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (e : Section34CompactEdgeIndex K K) (s : Finset E3) :
    compactDualSplitDisk M K hKM e ∩ compactDualResidualCell M K s ⊆
      compactDualCutBoundary M K hKM (.splitDisk e) := by
  have havoid : compactDualResidualCell M K s ⊆
      (interior (compactDualNeighborhood M K))ᶜ := by
    apply closure_minimal
    · exact fun _ hx hxi => hx.2 (interior_subset hxi)
    · exact isOpen_interior.isClosed_compl
  rw [compactDualCutBoundary_splitDisk_eq_inter_frontier M K hM hKM hint e]
  rintro x ⟨hxD, hxR⟩
  exact ⟨hxD, subset_closure (compactDualSplitDisk_subset_neighborhood M K hKM e hxD),
    havoid hxR⟩

open Classical in
theorem compactDualSplitDisk_inter_cell_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (e : Section34CompactEdgeIndex K K)
    (l : Section34CompactLabelOf K K) (hl : section34BoundedDim l ≤ 2)
    (hne : .splitDisk e ≠ l) :
    compactDualSplitDisk M K hKM e ∩ compactDualCutCell M K hKM l ⊆
      compactDualCutBoundary M K hKM (.splitDisk e) ∪ compactDualCutBoundary M K hKM l := by
  intro x hx
  cases l with
  | vertexBall w => simp [section34BoundedDim] at hl
  | tetraBall t => simp [section34BoundedDim] at hl
  | splitDisk f =>
    exact (Set.disjoint_left.mp (disjoint_compactDualSplitDisk M K hKM e f
      (fun h => hne (congrArg Section34BoundedLabel.splitDisk h))) hx.1 hx.2).elim
  | faceDisk s =>
    exact Or.inl (compactDualSplitDisk_inter_residual_subset_boundary M K hM hKM hint e s.1 hx)
  | patch p =>
    exact Or.inl (compactDualSplitDisk_inter_residual_subset_boundary M K hM hKM hint e
      p.1.1.1 ⟨hx.1, hx.2.1⟩)
  | faceArc a =>
    exact Or.inl (compactDualSplitDisk_inter_residual_subset_boundary M K hM hKM hint e
      a.1.1.1 ⟨hx.1, hx.2.2⟩)
  | edgeArc i =>
    exact Or.inl (compactDualSplitDisk_inter_residual_subset_boundary M K hM hKM hint e
      i.1.1.1 ⟨hx.1, hx.2.1⟩)
  | markedPoint p =>
    exact Or.inl (compactDualSplitDisk_inter_residual_subset_boundary M K hM hKM hint e
      p.1.1.1 ⟨hx.1, hx.2.2⟩)
  | outerFace o =>
    exact Or.inr (compactDualOuterFace_inter_cell_subset_boundary M K hM hK hKM hint o
      (.splitDisk e) (by simp [section34BoundedDim]) (by simp) ⟨hx.2, hx.1⟩)
  | outerArc q =>
    by_cases heq : e = q.1
    · subst e
      exact Or.inl (compactDualOuterArc_subset_splitBoundary M K hKM q hx.2)
    · exact (Set.disjoint_left.mp (disjoint_compactDualSplitDisk M K hKM e q.1 heq) hx.1
        (compactDualOuterArc_subset_splitDisk M K hKM q hx.2)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
