/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualRecognition
import DifferentialGeometry.Topology.RegularClosed

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem compact_vertex_centroid_injective
    (K : Geometry.SimplicialComplex ℝ E3) :
    Function.Injective (fun w : Section34CompactVertexIndex K K => w.1.centroid ℝ id) := by
  intro w v h
  change w.1.centroid ℝ id = v.1.centroid ℝ id at h
  apply Subtype.ext
  rw [← singleton_centroid_eq_compactVertexIndex w,
    ← singleton_centroid_eq_compactVertexIndex v, h]

theorem compactDualVertexBall_inter_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (w v : Section34CompactVertexIndex K K) (hwv : w ≠ v) :
    compactDualVertexBall M K w ∩ compactDualVertexBall M K v ⊆
      compactDualCutBoundary M K hKM (.vertexBall w) := by
  classical
  let : DecidableEq E3 := Classical.decEq E3
  let L := restrict K (section34CompactGraphSkeleton K)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 :=
    fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs
  have hvertex (p : Section34CompactVertexIndex K K) : {p.1.centroid ℝ id} ∈ L.faces := by
    rw [singleton_centroid_eq_compactVertexIndex p]
    exact ⟨p.2.1, p.2.2.2⟩
  have hne : w.1.centroid ℝ id ≠ v.1.centroid ℝ id :=
    fun h => hwv (compact_vertex_centroid_injective K h)
  rw [compactDualCutBoundary_vertexBall_eq_frontier M K hKM hM w]
  change (graphDualCell M L (w.1.centroid ℝ id)).space ∩
    (graphDualCell M L (v.1.centroid ℝ id)).space ⊆
      frontier (graphDualCell M L (w.1.centroid ℝ id)).space
  by_cases he : {w.1.centroid ℝ id, v.1.centroid ℝ id} ∈ L.faces
  · have hI : IsPLBall 2 ((graphDualCell M L (w.1.centroid ℝ id)).space ∩
        (graphDualCell M L (v.1.centroid ℝ id)).space) := by
      rw [graphDualCell_space_inter M L hLM hcard hne he]
      exact hM.isPLBall_splittingDisk M (hLM he) (k := 1)
        (Finset.card_pair hne) (by decide)
    exact (hM.isPLBall_graphDualCell M L hLM hcard (hvertex v)).inter_subset_frontier_of_isPLBall
      hI (by decide)
  · rw [graphDualCell_space_inter_eq_empty M L hLM hcard (hvertex w) (hvertex v) hne he]
    exact empty_subset _

theorem compactDualVertexBall_inter_residual_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (w : Section34CompactVertexIndex K K) (s : Finset E3) :
    compactDualVertexBall M K w ∩ compactDualResidualCell M K s ⊆
      compactDualCutBoundary M K hKM (.vertexBall w) := by
  rw [compactDualCutBoundary_vertexBall_eq_frontier M K hKM hM w]
  have havoid : compactDualResidualCell M K s ⊆
      (interior (compactDualNeighborhood M K))ᶜ := by
    apply closure_minimal
    · exact fun _ hx hxi => hx.2 (interior_subset hxi)
    · exact isOpen_interior.isClosed_compl
  rintro x ⟨hxV, hxR⟩
  exact ⟨subset_closure hxV, fun hxi => havoid hxR
    (interior_mono (compactDualVertexBall_subset_neighborhood M K w) hxi)⟩

theorem compactDualResidualCell_inter_neighborhood_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (t : Section34CompactSimplexIndex K 4) :
    compactDualResidualCell M K t.1 ∩ compactDualNeighborhood M K ⊆
      compactDualCutBoundary M K hKM (.tetraBall t) := by
  classical
  rw [(isPLCellOn_compactDualTetraBall M K hKM t).boundary_eq_frontier]
  change compactDualResidualCell M K t.1 ∩ compactDualNeighborhood M K ⊆
    frontier (compactDualResidualCell M K t.1)
  rintro x ⟨hxR, hxN⟩
  obtain ⟨v, hv, hxV⟩ := mem_iUnion₂.mp hxN
  let L := restrict K (section34CompactGraphSkeleton K)
  let V := (graphDualCell M L v).space
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hvL : {v} ∈ L.faces := ⟨hv,
    convexHull_subset_section34CompactGraphSkeleton hv (by simp)⟩
  have hV : IsPLBall 3 V := hM.isPLBall_graphDualCell M L hLM
    (fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs) hvL
  have hVN : V ⊆ compactDualNeighborhood M K := subset_iUnion₂_of_subset v hv subset_rfl
  have hsub : compactDualResidualCell M K t.1 ⊆
      closure (convexHull ℝ (t.1 : Set E3) \ V) :=
    closure_mono (sdiff_subset_sdiff_right hVN)
  have hint : interior (compactDualResidualCell M K t.1) ⊆ Vᶜ :=
    (interior_mono hsub).trans
      (DifferentialGeometry.Topology.interior_closure_sdiff_subset_compl hV.closure_interior)
  exact ⟨subset_closure hxR, fun hxi => hint hxi hxV⟩

theorem compactDualResidualCell_inter_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s t : Section34CompactSimplexIndex K 4) (hst : s ≠ t) :
    compactDualResidualCell M K s.1 ∩ compactDualResidualCell M K t.1 ⊆
      compactDualCutBoundary M K hKM (.tetraBall s) := by
  classical
  rw [(isPLCellOn_compactDualTetraBall M K hKM s).boundary_eq_frontier]
  have hsub (u : Section34CompactSimplexIndex K 4) :
      compactDualResidualCell M K u.1 ⊆ convexHull ℝ (u.1 : Set E3) :=
    closure_minimal sdiff_subset (u.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  rintro x ⟨hxs, hxt⟩
  refine ⟨subset_closure hxs, fun hxint => ?_⟩
  have hxopen : x ∈ openSimplex s.1 := by
    rw [← interior_convexHull_eq_openSimplex (K.indep s.2.1)
      (by rw [s.2.2, finrank_euclideanSpace_fin])]
    exact interior_mono (hsub s) hxint
  have hs : s.1 ⊆ t.1 :=
    face_subset_of_mem_openSimplex_of_mem_convexHull K s.2.1 t.2.1 hxopen (hsub t hxt)
  exact hst (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [s.2.2, t.2.2])))

theorem compactDualCutCell_inter_subset_boundary_of_dim_eq_three
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (l m : Section34CompactLabelOf K K) (hl : section34BoundedDim l = 3)
    (hm : section34BoundedDim m = 3) (hlm : l ≠ m) :
    compactDualCutCell M K hKM l ∩ compactDualCutCell M K hKM m ⊆
      compactDualCutBoundary M K hKM l ∪ compactDualCutBoundary M K hKM m := by
  rcases section34BoundedDim_eq_three hl with ⟨w, rfl⟩ | ⟨s, rfl⟩ <;>
    rcases section34BoundedDim_eq_three hm with ⟨v, rfl⟩ | ⟨t, rfl⟩
  · exact (compactDualVertexBall_inter_subset_boundary M K hKM hM w v
      (fun h => hlm (congrArg Section34BoundedLabel.vertexBall h))).trans subset_union_left
  · exact (compactDualVertexBall_inter_residual_subset_boundary M K hKM hM w t.1).trans
      subset_union_left
  · intro x hx
    exact Or.inr (compactDualVertexBall_inter_residual_subset_boundary M K hKM hM v s.1
      ⟨hx.2, hx.1⟩)
  · exact (compactDualResidualCell_inter_subset_boundary M K hKM s t
      (fun h => hlm (congrArg Section34BoundedLabel.tetraBall h))).trans subset_union_left

end DifferentialGeometry.Topology.PiecewiseLinear
