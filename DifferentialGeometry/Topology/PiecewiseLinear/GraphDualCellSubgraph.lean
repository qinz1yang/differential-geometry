/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellSurface
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhood_restrict_right
    (M A L : Geometry.SimplicialComplex ℝ E) (hAM : A.faces ⊆ M.faces)
    (hLM : L.faces ⊆ M.faces) :
    derivedNeighborhood A (restrict L A.space) = derivedNeighborhood A L := by
  ext u
  constructor
  · rintro ⟨D, hD, hne, hmeet, rfl⟩
    refine ⟨D, hD, hne, ?_, rfl⟩
    intro e he
    obtain ⟨s, hs, hse⟩ := hmeet e he
    exact ⟨s, hs.1, hse⟩
  · rintro ⟨D, hD, hne, hmeet, rfl⟩
    refine ⟨D, hD, hne, ?_, rfl⟩
    intro e he
    obtain ⟨s, hs, hse⟩ := hmeet e he
    have hcA : s.centroid ℝ id ∈ A.space := by
      exact (barycentricSubdivision_isSubdivision A).space_eq ▸
        (barycentricSubdivision A).subset_space (hD.mem_faces he) hse
    have hsA : s ∈ A.faces := mem_faces_of_mem_openSimplex_of_mem_space hAM (hLM hs)
      (centroid_mem_openSimplex_of_mem_faces M s (hLM hs)) hcA
    exact ⟨s, ⟨hs, A.convexHull_subset_space hsA⟩, hse⟩

open Classical in
theorem graphDualCell_restrict_right
    (M A L : Geometry.SimplicialComplex ℝ E) (hAM : A.faces ⊆ M.faces)
    (hLM : L.faces ⊆ M.faces) (v : E) :
    graphDualCell A (restrict L A.space) v = graphDualCell A L v := by
  simp only [graphDualCell, derivedNeighborhood_restrict_right M A L hAM hLM]

open Classical in
theorem graphDualCell_space_inter_subcomplex_restrict
    (M A L : Geometry.SimplicialComplex ℝ E) (hAM : A.faces ⊆ M.faces)
    (hLM : L.faces ⊆ M.faces) {v : E} (hv : {v} ∈ A.faces) :
    (graphDualCell M L v).space ∩ A.space =
      (graphDualCell A (restrict L A.space) v).space := by
  rw [graphDualCell_space_inter_subcomplex M A L hAM hv,
    graphDualCell_restrict_right M A L hAM hLM v]

open Classical in
theorem graphDualCell_inter_boundaryComplex
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {v : E} (hv : {v} ∈ (boundaryComplex 3 K).faces) :
    (graphDualCell K L v).space ∩ (boundaryComplex 3 K).space =
      (graphDualCell (boundaryComplex 3 K)
        (restrict L (boundaryComplex 3 K).space) v).space :=
  graphDualCell_space_inter_subcomplex_restrict K (boundaryComplex 3 K) L
    (boundaryComplex_faces_subset 3 K) hLK hv

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_inter_boundaryComplex
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces)
    (hvbd : {v} ∈ (boundaryComplex 3 K).faces) :
    IsPLBall 2 ((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) := by
  rw [graphDualCell_inter_boundaryComplex K L hLK hvbd]
  let B := boundaryComplex 3 K
  let G := restrict L B.space
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifoldWithBoundary 2 B :=
    (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  have hGB : G.faces ⊆ B.faces := by
    intro s hs
    exact ((mem_restrict_faces_iff_of_faces_subset K L B hLK
      (boundaryComplex_faces_subset 3 K)).mp hs).2
  exact hB.isPLBall_graphDualCell_two B G hGB (fun s hs => hcard s hs.1)
    ⟨hv, B.convexHull_subset_space hvbd⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.graphDualCell_inter_boundaryComplex_subset_boundary
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    (graphDualCell K L v).space ∩ (boundaryComplex 3 K).space ⊆
      (boundaryComplex 3 (graphDualCell K L v)).space := by
  let _ : Finite (graphDualCell K L v).faces := (graphDualCell_faces_finite K L v).to_subtype
  exact inter_boundaryComplex_space_subset_of_subset K (graphDualCell K L v) hK
    (hK.isPLBall_graphDualCell K L hLK hcard hv).isCombinatorialManifoldWithBoundary
    ((graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L))

end DifferentialGeometry.Topology.PiecewiseLinear
