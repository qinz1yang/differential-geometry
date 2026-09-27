/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeSphereBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellSurfaceTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSubcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem centroid_mem_upperLink_of_ssubset
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (ht : t ∈ K.faces) (hst : s ⊂ t) : t.centroid ℝ id ∈ (upperLink K s).space := by
  have hflag : IsFlag K {t} := by
    refine ⟨fun e he => (Finset.mem_singleton.mp he).symm ▸ ht, ?_⟩
    intro e he f hf
    rw [Finset.mem_singleton.mp he, Finset.mem_singleton.mp hf]
    exact Or.inl subset_rfl
  have hmem : {t.centroid ℝ id} ∈ (upperLink K s).faces := by
    refine ⟨{t}, hflag, Finset.singleton_nonempty t, ?_, by simp⟩
    intro e he
    exact Finset.mem_singleton.mp he ▸ hst
  exact (upperLink K s).subset_space hmem (Finset.mem_singleton_self _)

open Classical in
theorem graphDualCell_inter_subcomplex_eq_dualCell
    (M H L : Geometry.SimplicialComplex ℝ E) [Finite H.faces]
    (hHM : H.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces) (hHL : H.faces ⊆ L.faces)
    {v : E} (hvH : {v} ∈ H.faces) :
    (graphDualCell M L v).space ∩ H.space = (dualCell H {v} hvH).space := by
  rw [graphDualCell_space_inter_subcomplex_restrict M H L hHM hLM hvH,
    restrict_eq_of_subcomplex L H hHL, graphDualCell_space_eq_inter H H hvH,
    closedStar_barycentricSubdivision_eq_dualCell H hvH]
  have hN : (derivedNeighborhood H H).space = H.space :=
    Subset.antisymm (derivedNeighborhood_space_subset H H)
      (subcomplex_space_subset_derivedNeighborhood Subset.rfl)
  rw [hN]
  apply inter_eq_right.mpr
  rw [← (barycentricSubdivision_isSubdivision H).space_eq]
  exact space_mono_of_faces_subset (dualCell_faces_subset H hvH)

variable [FiniteDimensional ℝ E]

open Classical in
theorem boundary_dualCell_vertex_eq_pair
    (H : Geometry.SimplicialComplex ℝ E) [Finite H.faces]
    (hH : IsCombinatorialManifold 1 H) {u v w : E}
    (hvH : {v} ∈ H.faces) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h0 : {u, v} ∈ H.faces) (h1 : {v, w} ∈ H.faces) :
    (boundaryComplex 1 (dualCell H {v} hvH)).space =
      {({u, v} : Finset E).centroid ℝ id, ({v, w} : Finset E).centroid ℝ id} := by
  let _ : Finite (upperLink H {v}).faces := (upperLink_faces_finite H {v}).to_subtype
  have hbase : IsPLSphere 0 (upperLink H {v}).space :=
    hH.isPLSphere_upperLink H hvH (k := 0) (Finset.card_singleton _) (by omega)
  have hbd : (boundaryComplex 1 (dualCell H {v} hvH)).space = (upperLink H {v}).space :=
    (isConeBase_upperLink H hvH).boundaryComplex_space_of_isPLSphere hbase
  rw [hbd]
  have hp : ({u, v} : Finset E).centroid ℝ id ∈ (upperLink H {v}).space :=
    centroid_mem_upperLink_of_ssubset H h0 (Finset.ssubset_iff_subset_ne.mpr
      ⟨by simp, fun h => by have hc := congrArg Finset.card h; simp [huv] at hc⟩)
  have hq : ({v, w} : Finset E).centroid ℝ id ∈ (upperLink H {v}).space :=
    centroid_mem_upperLink_of_ssubset H h1 (Finset.ssubset_iff_subset_ne.mpr
      ⟨by simp, fun h => by have hc := congrArg Finset.card h; simp [hvw] at hc⟩)
  have hpq : ({u, v} : Finset E).centroid ℝ id ≠ ({v, w} : Finset E).centroid ℝ id := by
    apply centroid_ne_centroid_of_ne H h0 h1
    intro heq
    have hu : u ∈ ({v, w} : Finset E) := heq ▸ Finset.mem_insert_self u {v}
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    exact hu.elim huv huw
  have hsub : {({u, v} : Finset E).centroid ℝ id,
      ({v, w} : Finset E).centroid ℝ id} ⊆ (upperLink H {v}).space := by
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · exact mem_singleton_iff.mp hx ▸ hq
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ hbase.finite_of_zero).symm
  obtain ⟨a, b, hab, heq⟩ := isPLSphere_zero_iff.mp hbase
  rw [heq, ncard_pair hab, ncard_pair hpq]

open Classical in
theorem frontier_graphDualCell_inter_curve_subset_boundary
    (M H L : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hH : IsCombinatorialManifold 1 H)
    (hHM : H.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces) (hHL : H.faces ⊆ L.faces)
    (hcard : ∀ e ∈ L.faces, e.card ≤ 2) (hHint : H.space ⊆ interior M.space)
    {v : E} (hvH : {v} ∈ H.faces) :
    frontier (graphDualCell M L v).space ∩ H.space ⊆
      (boundaryComplex 1 (dualCell H {v} hvH)).space := by
  let _ : Finite H.faces := ((Set.toFinite M.faces).subset hHM).to_subtype
  let _ : Finite (upperLink H {v}).faces := (upperLink_faces_finite H {v}).to_subtype
  let _ : Finite (graphDualCell M L v).faces :=
    (graphDualCell_faces_finite M L v).to_subtype
  have hbase : IsPLSphere 0 (upperLink H {v}).space :=
    hH.isPLSphere_upperLink H hvH (k := 0) (Finset.card_singleton _) (by omega)
  have hbd : (boundaryComplex 1 (dualCell H {v} hvH)).space = (upperLink H {v}).space :=
    (isConeBase_upperLink H hvH).boundaryComplex_space_of_isPLSphere hbase
  rw [hbd]
  rintro x ⟨hxFr, hxH⟩
  have hxC : x ∈ (graphDualCell M L v).space :=
    (SimplicialComplex.isCompact_geometricSpace _).isClosed.frontier_subset hxFr
  have hxN : x ∈ interior (derivedNeighborhood M L).space := by
    have hxL := space_mono_of_faces_subset hHL hxH
    obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (derivedNeighborhood_mem_nhdsWithin hLM hxL)
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (Filter.inter_mem hU (mem_interior_iff_mem_nhds.mp (hHint hxH))) hUsub)
  have hxD : x ∈ ⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2},
      (splittingDisk M e.1 (hLM e.2.1)).space := by
    by_contra hn
    exact (frontier_graphDualCell_sdiff_splittingDisk_subset M L hLM hcard
      (hHL hvH) ⟨hxFr, hn⟩).2 hxN
  obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
  have heH : e.1 ∈ H.faces := mem_faces_of_dualCell_inter_subcomplex M H hHM
    (hLM e.2.1) (splittingDisk_space_subset_dualCell M (hLM e.2.1) hxe) hxH
  have hve : v ∈ e.1 := mem_of_graphDualCell_inter_splittingDisk_nonempty M L
    (hHM hvH) (hLM e.2.1) ⟨x, hxC, hxe⟩
  have hsplit : x ∈ (splittingDisk H e.1 heH).space := by
    rw [← splittingDisk_space_inter_subcomplex M H hHM heH]
    exact ⟨hxe, hxH⟩
  have hxdual := splittingDisk_space_subset_dualCell H heH hsplit
  have hsingle := dualCell_space_eq_singleton_of_card H heH
    (fun t ht => (hH.card_le H ht).trans_eq e.2.2.symm)
  have hxc : x = e.1.centroid ℝ id := by rwa [hsingle, mem_singleton_iff] at hxdual
  rw [hxc]
  apply centroid_mem_upperLink_of_ssubset H heH
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hve, ?_⟩
  intro heq
  have hc := congrArg Finset.card heq
  simp only [Finset.card_singleton, e.2.2] at hc
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
