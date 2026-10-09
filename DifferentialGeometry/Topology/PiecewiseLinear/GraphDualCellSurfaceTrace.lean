/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualVertexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBoundaryCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem frontier_derivedNeighborhood_inter_subcomplex_subset_closure_sdiff
    (M F L : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hFM : F.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces)
    (hFint : F.space ⊆ interior M.space) :
    frontier (derivedNeighborhood M L).space ∩ F.space ⊆
      closure (F.space \ (derivedNeighborhood M L).space) := by
  let _ : Finite F.faces := ((Set.toFinite M.faces).subset hFM).to_subtype
  rintro x ⟨hxN, hxF⟩
  have hxR : x ∈ closure (M.space \ (derivedNeighborhood M L).space) := by
    rw [frontier_eq_closure_inter_closure] at hxN
    apply mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨y, hyO, hyN⟩ := mem_closure_iff.mp hxN.2 (O ∩ interior M.space)
      (hO.inter isOpen_interior) ⟨hxO, hFint hxF⟩
    exact ⟨y, hyO.1, interior_subset hyO.2, hyN⟩
  rw [closure_space_sdiff_derivedNeighborhood_space (A := M) Subset.rfl hLM] at hxR
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hxR
  have hxsD : x ∈ (dualCell (barycentricSubdivision M) {s.centroid ℝ id}
      (singleton_centroid_mem_barycentricSubdivision M hs.1)).space := by
    rwa [derivedNeighborhoodCell_eq_dualCell M hs.1] at hxs
  have hcsF := mem_faces_of_dualCell_inter_subcomplex
    (barycentricSubdivision M) (barycentricSubdivision F)
    (barycentricSubdivision_faces_subset hFM)
    (singleton_centroid_mem_barycentricSubdivision M hs.1) hxsD
    ((barycentricSubdivision_isSubdivision F).space_eq.symm ▸ hxF)
  obtain ⟨t, ht, htc⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision F hcsF
  have hts := injOn_faces_of_mem_openSimplex M
    (centroid_mem_openSimplex_of_mem_faces M) (hFM ht) hs.1 htc
  have hsF : s ∈ F.faces := hts ▸ ht
  have hxcell : x ∈ (derivedNeighborhoodCell F s).space := by
    rw [← derivedNeighborhoodCell_inter_subcomplex M F hFM hsF]
    exact ⟨hxs, hxF⟩
  have hxR' : x ∈ closure (F.space \ (derivedNeighborhood F L).space) := by
    rw [closure_space_sdiff_derivedNeighborhood_space hFM hLM]
    exact mem_iUnion₂.mpr ⟨s, ⟨hsF, hs.2⟩, hxcell⟩
  have hdiff : F.space \ (derivedNeighborhood F L).space =
      F.space \ (derivedNeighborhood M L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex M F L hFM]
    ext y
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rwa [hdiff] at hxR'

variable [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_inter_surface
    (M F L : Geometry.SimplicialComplex ℝ E) [Finite F.faces]
    (hF : IsCombinatorialManifoldWithBoundary 2 F)
    (hFM : F.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces)
    (hcard : ∀ e ∈ L.faces, e.card ≤ 2) {v : E}
    (hvF : {v} ∈ F.faces) (hvL : {v} ∈ L.faces) :
    IsPLBall 2 ((graphDualCell M L v).space ∩ F.space) := by
  rw [graphDualCell_space_inter_subcomplex_restrict M F L hFM hLM hvF]
  exact hF.isPLBall_graphDualCell_two F (restrict L F.space)
    (fun e he => ((mem_restrict_faces_iff_of_faces_subset M L F hLM hFM).mp he).2)
    (fun e he => hcard e he.1) ⟨hvL, F.convexHull_subset_space hvF⟩

open Classical in
theorem frontier_graphDualCell_inter_surface_subset_boundary
    (M F L : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hF : IsCombinatorialManifoldWithBoundary 2 F)
    (hFM : F.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces)
    (hcard : ∀ e ∈ L.faces, e.card ≤ 2) (hFint : F.space ⊆ interior M.space)
    {v : E} (hvF : {v} ∈ F.faces) (hvL : {v} ∈ L.faces) :
    frontier (graphDualCell M L v).space ∩ F.space ⊆
      (boundaryComplex 2 (graphDualCell F (restrict L F.space) v)).space := by
  let G := restrict L F.space
  let B := graphDualCell F G v
  let _ : Finite F.faces := ((Set.toFinite M.faces).subset hFM).to_subtype
  let _ : Finite B.faces := (graphDualCell_faces_finite F G v).to_subtype
  let _ : Finite (graphDualCell M L v).faces :=
    (graphDualCell_faces_finite M L v).to_subtype
  have hGF : G.faces ⊆ F.faces := fun e he =>
    ((mem_restrict_faces_iff_of_faces_subset M L F hLM hFM).mp he).2
  have hGcard : ∀ e ∈ G.faces, e.card ≤ 2 := fun e he => hcard e he.1
  have hvG : {v} ∈ G.faces := ⟨hvL, F.convexHull_subset_space hvF⟩
  have hB : IsPLBall 2 B.space := hF.isPLBall_graphDualCell_two F G hGF hGcard hvG
  have hBF : B.space ⊆ F.space :=
    (graphDualCell_space_subset F G v).trans (derivedNeighborhood_space_subset F G)
  have htrace : (graphDualCell M L v).space ∩ F.space = B.space :=
    graphDualCell_space_inter_subcomplex_restrict M F L hFM hLM hvF
  rintro x ⟨hxFr, hxF⟩
  have hxC : x ∈ (graphDualCell M L v).space :=
    (SimplicialComplex.isCompact_geometricSpace _).isClosed.frontier_subset hxFr
  have hxB : x ∈ B.space := htrace ▸ ⟨hxC, hxF⟩
  by_cases hxD : x ∈ ⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2},
      (splittingDisk M e.1 (hLM e.2.1)).space
  · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
    have heF : e.1 ∈ F.faces := mem_faces_of_dualCell_inter_subcomplex M F hFM
      (hLM e.2.1) (splittingDisk_space_subset_dualCell M (hLM e.2.1) hxe) hxF
    have heG : e.1 ∈ G.faces := ⟨e.2.1, F.convexHull_subset_space heF⟩
    have hve : v ∈ e.1 := mem_of_graphDualCell_inter_splittingDisk_nonempty M L
      (hLM hvL) (hLM e.2.1) ⟨x, hxC, hxe⟩
    obtain ⟨w, hwe, hwv⟩ := Finset.exists_mem_ne
      (show 1 < e.1.card by rw [e.2.2]; norm_num) v
    have hwG : {w} ∈ G.faces := G.down_closed heG
      (Finset.singleton_subset_iff.mpr hwe) (Finset.singleton_nonempty w)
    have hsplit : x ∈ (splittingDisk F e.1 heF).space := by
      rw [← splittingDisk_space_inter_subcomplex M F hFM heF]
      exact ⟨hxe, hxF⟩
    have hinter : B.space ∩ (graphDualCell F G w).space =
        (splittingDisk F e.1 heF).space :=
      graphDualCell_space_inter_of_mem F G hGF hGcard heG hve hwe hwv.symm
    have hI : IsPLBall 1 (B.space ∩ (graphDualCell F G w).space) := by
      rw [hinter]
      exact hF.isPLBall_splittingDisk F heF e.2.2 (by norm_num : 1 ≤ 1)
    exact hF.inter_subset_boundaryComplex_of_isPLBall B hB hBF
      (hF.isPLBall_graphDualCell_two F G hGF hGcard hwG)
      ((graphDualCell_space_subset F G w).trans (derivedNeighborhood_space_subset F G))
      hI (hinter.symm ▸ hsplit)
  · have hxN := frontier_graphDualCell_sdiff_splittingDisk_subset M L hLM hcard hvL
      ⟨hxFr, hxD⟩
    have hxR := frontier_derivedNeighborhood_inter_subcomplex_subset_closure_sdiff
      M F L hFM hLM hFint ⟨hxN, hxF⟩
    have hrem : F.space \ (derivedNeighborhood M L).space ⊆ F.space \ B.space := by
      rintro y ⟨hyF, hyN⟩
      exact ⟨hyF, fun hyB => hyN (graphDualCell_space_subset M L v
        (htrace.symm ▸ hyB).1)⟩
    have hBsub : B.faces ⊆ (secondDerived F).faces :=
      (graphDualCell_faces_subset F G v).trans (derivedNeighborhood_faces_subset F G)
    apply inter_closure_sdiff_space_subset_boundaryComplex (secondDerived F) B
      hF.secondDerived hB.isCombinatorialManifoldWithBoundary hBsub
    rw [(secondDerived_isSubdivision F).space_eq]
    exact ⟨hxB, closure_mono hrem hxR⟩

open Classical in
theorem boundary_graphDualCell_surface_subset_boundary_union_frontier
    (M F L : Geometry.SimplicialComplex ℝ E) [Finite F.faces]
    (hF : IsCombinatorialManifoldWithBoundary 2 F)
    (hFM : F.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces)
    (hcard : ∀ e ∈ L.faces, e.card ≤ 2) {v : E}
    (hvF : {v} ∈ F.faces) (hvL : {v} ∈ L.faces) :
    (boundaryComplex 2 (graphDualCell F (restrict L F.space) v)).space ⊆
      (boundaryComplex 2 F).space ∪ frontier (graphDualCell M L v).space := by
  let G := restrict L F.space
  let B := graphDualCell F G v
  let _ : Finite B.faces := (graphDualCell_faces_finite F G v).to_subtype
  have hGF : G.faces ⊆ F.faces := fun e he =>
    ((mem_restrict_faces_iff_of_faces_subset M L F hLM hFM).mp he).2
  have hGcard : ∀ e ∈ G.faces, e.card ≤ 2 := fun e he => hcard e he.1
  have hvG : {v} ∈ G.faces := ⟨hvL, F.convexHull_subset_space hvF⟩
  have hB : IsPLBall 2 B.space := hF.isPLBall_graphDualCell_two F G hGF hGcard hvG
  have htrace : (graphDualCell M L v).space ∩ F.space = B.space :=
    graphDualCell_space_inter_subcomplex_restrict M F L hFM hLM hvF
  have hBsub : B.faces ⊆ (secondDerived F).faces :=
    (graphDualCell_faces_subset F G v).trans (derivedNeighborhood_faces_subset F G)
  have hcover := boundaryComplex_space_subset_boundary_union_closure_sdiff
    (secondDerived F) B hF.secondDerived hB.isCombinatorialManifoldWithBoundary hBsub
  rw [boundaryComplex_space_of_isSubdivision F (secondDerived F) hF
    (secondDerived_isSubdivision F), (secondDerived_isSubdivision F).space_eq] at hcover
  intro x hx
  rcases hcover hx with hxF | hxR
  · exact Or.inl hxF
  · right
    have hxB := boundaryComplex_space_subset 2 B hx
    have hxC : x ∈ (graphDualCell M L v).space := (htrace.symm ▸ hxB).1
    refine ⟨subset_closure hxC, ?_⟩
    have hrem : F.space \ B.space ⊆ (graphDualCell M L v).spaceᶜ := by
      rintro y ⟨hyF, hyB⟩ hyC
      exact hyB (htrace ▸ ⟨hyC, hyF⟩)
    have h := closure_mono hrem hxR
    rwa [closure_compl] at h

end DifferentialGeometry.Topology.PiecewiseLinear
