/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.SplitDiskCenter
import DifferentialGeometry.Topology.PiecewiseLinear.TubeOfGraphDualCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem IsTube.splitDisk_isPseudoCell
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) :
    IsPseudoCell (D e) (D e \ Dbd e) (Dbd e) (e.centroid ℝ id) := by
  obtain ⟨r, hr, hrim, hcenter⟩ :=
    ht.exists_centered_splitDisk_parametrization he hcard
  have hmem : e.centroid ℝ id ∈ D e \ r '' stdSimplexBoundary 2 := by
    rw [← hcenter, ← hr.image_openSimplex_stdVertices]
    exact ⟨stdCenter 1, stdCenter_mem_openSimplex 1, rfl⟩
  simpa only [hrim] using hr.isPseudoCell_of_mem_interior hmem

open Classical in
theorem exists_isTube_with_pseudoCell_splitDisks :
    ∃ (K : Geometry.SimplicialComplex ℝ E3) (N : Set E3)
      (C : E3 → Set E3) (D Dbd : Finset E3 → Set E3)
      (h : E3 → E3) (N' : Set E3),
      IsTube K N C D Dbd h N' ∧
      (∃ e ∈ K.faces, e.card = 2) ∧
      ∀ e ∈ K.faces, e.card = 2 →
        IsPseudoCell (D e) (D e \ Dbd e) (Dbd e) (e.centroid ℝ id) := by
  obtain ⟨K, N, C, D, Dbd, h, N', ht⟩ := exists_isTube
  exact ⟨K, N, C, D, Dbd, h, N', ht, ht.hasEdge,
    fun e he hcard => ht.splitDisk_isPseudoCell he hcard⟩

open Classical in
theorem exists_isTube_id_with_pseudoCell_splitDisks :
    ∃ (K : Geometry.SimplicialComplex ℝ E3) (N : Set E3)
      (C : E3 → Set E3) (D Dbd : Finset E3 → Set E3),
      IsTube K N C D Dbd id N ∧
      (∃ e ∈ K.faces, e.card = 2) ∧
      ∀ e ∈ K.faces, e.card = 2 →
        IsPseudoCell (D e) (D e \ Dbd e) (Dbd e) (e.centroid ℝ id) := by
  obtain ⟨K, N, C, D, Dbd, h, N', ht⟩ := exists_isTube
  have hid : IsEmbedding (N.domRestrict (id : E3 → E3)) := by
    simpa only [domRestrict_id] using
      (Topology.IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : N → E3))
  have ht₀ : IsTube K N C D Dbd id N := by
    simpa only [image_id] using ht.of_isEmbedding hid
  exact ⟨K, N, C, D, Dbd, ht₀, ht₀.hasEdge,
    fun e he hcard => ht₀.splitDisk_isPseudoCell he hcard⟩

end DifferentialGeometry.Topology.PiecewiseLinear
