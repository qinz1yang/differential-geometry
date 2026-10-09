/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualFaceSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualIncidence

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem compact_incident_of_subset {s t : Finset E3} (h : s ⊆ t) :
    Section34Incident s t :=
  (Finset.coe_subset.mpr h).trans (subset_convexHull ℝ _)

open Classical in
theorem subset_of_nonempty_compactDualSplitDisk_inter_convexHull
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (e : Section34CompactEdgeIndex K K) {s : Finset E3} (hs : s ∈ K.faces)
    (hinter : (compactDualSplitDisk M K hKM e ∩ convexHull ℝ (s : Set E3)).Nonempty) :
    e.1 ⊆ s := by
  obtain ⟨x, hxD, hxs⟩ := hinter
  have hxA := splittingDisk_space_subset_dualCell M (hKM e.2.1) hxD
  exact subset_of_mem_dualCell_of_mem_convexHull M (hKM e.2.1) (hKM hs) hxA hxs

open Classical in
theorem section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (e : Section34CompactEdgeIndex K K) {s : Finset E3} (hs : s ∈ K.faces)
    (hinter : (compactDualSplitDisk M K hKM e ∩ compactDualResidualCell M K s).Nonempty) :
    Section34Incident e.1 s := by
  apply compact_incident_of_subset
  apply subset_of_nonempty_compactDualSplitDisk_inter_convexHull M K hKM e hs
  obtain ⟨x, hxD, hxR⟩ := hinter
  exact ⟨x, hxD, closure_minimal sdiff_subset
    (s.finite_toSet.isCompact_convexHull ℝ).isClosed hxR⟩

open Classical in
theorem section34Incident_of_nonempty_compactDualFaceDisk_inter_residual
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3)
    {t : Finset E3} (ht : t ∈ K.faces)
    (hinter : (compactDualResidualCell M K s.1 ∩ compactDualResidualCell M K t).Nonempty) :
    Section34Incident s.1 t := by
  obtain ⟨x, hxS, hxT⟩ := hinter
  have hxt : x ∈ convexHull ℝ (t : Set E3) := closure_minimal sdiff_subset
    (t.finite_toSet.isCompact_convexHull ℝ).isClosed hxT
  exact compact_incident_of_subset (face_subset_of_mem_openSimplex_of_mem_convexHull K
    s.2.1 ht (compactDualFaceDisk_subset_openSimplex M K hKM s hxS) hxt)

open Classical in
theorem section34Incident_of_nonempty_compactDualVertexBall_inter_faceDisk
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (w : Section34CompactVertexIndex K K)
    (s : Section34CompactSimplexIndex K 3)
    (hinter : (compactDualVertexBall M K w ∩ compactDualResidualCell M K s.1).Nonempty) :
    Section34Incident w.1 s.1 := by
  obtain ⟨x, hxV, hxF⟩ := hinter
  have hxS : x ∈ convexHull ℝ (s.1 : Set E3) :=
    openSimplex_subset_convexHull _ (compactDualFaceDisk_subset_openSimplex M K hKM s hxF)
  have hvs : w.1.centroid ℝ id ∈ s.1 := by
    by_contra hvs
    have hzero := graphDualCell_space_inter_convexHull_eq_empty
      (restrict K (section34CompactGraphSkeleton K))
      (hKM (centroid_mem_vertices_compactVertexIndex w)) (hKM s.2.1) hvs
    exact (eq_empty_iff_forall_notMem.mp hzero) x ⟨hxV, hxS⟩
  apply compact_incident_of_subset
  rw [← singleton_centroid_eq_compactVertexIndex w, Finset.singleton_subset_iff]
  exact hvs

end DifferentialGeometry.Topology.PiecewiseLinear
