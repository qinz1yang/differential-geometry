/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem mem_of_graphDualCell_inter_splittingDisk_nonempty
    (K L : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∈ K.faces)
    {e : Finset E} (he : e ∈ K.faces)
    (hinter : ((graphDualCell K L v).space ∩ (splittingDisk K e he).space).Nonempty) :
    v ∈ e := by
  classical
  obtain ⟨x, hxC, hxD⟩ := hinter
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (splittingDisk K e he) hxD
  have huK := splittingDisk_faces_subset K he hu
  have huC := mem_faces_of_mem_openSimplex_of_mem_space
    ((graphDualCell_faces_subset K L v).trans (derivedNeighborhood_faces_subset K L))
    huK hxu hxC
  obtain ⟨D, hD, hne, rfl⟩ := huK
  have hC := ((mem_graphDualCell_faces_iff_of_flag L hv hD hne).mp huC).2
  have hsplit := ((mem_splittingDisk_faces_iff_of_flag he hD hne).mp hu).2
  obtain ⟨s, hs⟩ := hne
  have hcent : e.centroid ℝ id ∈ (dualCell K {v} hv).space :=
    (dualCell K {v} hv).convexHull_subset_space (hC s hs)
      (subset_convexHull ℝ _ (hsplit s hs))
  exact Finset.singleton_subset_iff.mp
    (subset_of_mem_dualCell_of_mem_convexHull K hv he hcent
      (e.centroid_mem_convexHull (K.nonempty_of_mem_faces he)))

open Classical in
theorem disjoint_graphDualCell_splittingDisk_of_notMem
    (K L : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∈ K.faces)
    {e : Finset E} (he : e ∈ K.faces) (hve : v ∉ e) :
    Disjoint (graphDualCell K L v).space (splittingDisk K e he).space := by
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  exact hve (mem_of_graphDualCell_inter_splittingDisk_nonempty K L hv he ⟨x, hxC, hxD⟩)

open Classical in
theorem graphDualCell_triple_inter_eq_empty (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w z : E}
    (hv : {v} ∈ L.faces) (hw : {w} ∈ L.faces) (hz : {z} ∈ L.faces)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ((graphDualCell K L v).space ∩ (graphDualCell K L w).space) ∩
      (graphDualCell K L z).space = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxv, hxw⟩, hxz⟩
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (graphDualCell K L v) hxv
  have huK := derivedNeighborhood_faces_subset K L (graphDualCell_faces_subset K L v hu)
  have huw := mem_faces_of_mem_openSimplex_of_mem_space
    ((graphDualCell_faces_subset K L w).trans (derivedNeighborhood_faces_subset K L))
    huK hxu hxw
  have he := pair_mem_of_mem_graphDualCell_faces K L hL hcard hv hw hvw hu huw
  have hxD : x ∈ (splittingDisk K {v, w} (hL he)).space := by
    rw [← graphDualCell_space_inter K L hL hcard hvw he]
    exact ⟨hxv, hxw⟩
  have hzmem := mem_of_graphDualCell_inter_splittingDisk_nonempty K L (hL hz)
    (hL he) ⟨x, hxz, hxD⟩
  have hzpair : z = v ∨ z = w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hzmem
  rcases hzpair with h | h
  · exact hvz h.symm
  · exact hwz h.symm

end DifferentialGeometry.Topology.PiecewiseLinear
