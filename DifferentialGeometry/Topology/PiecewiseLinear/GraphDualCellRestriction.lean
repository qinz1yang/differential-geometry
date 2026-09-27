/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.StarIntersection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem dualCell_faces_subset_of_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ A.faces) :
    (dualCell A e he).faces ⊆ (dualCell K e (hAK he)).faces := by
  intro u hu
  obtain ⟨d, hd, hne, hsub, rfl⟩ := (mem_dualCell_faces_iff A he).mp hu
  exact (mem_dualCell_faces_iff K (hAK he)).mpr ⟨d, hd.of_le hAK, hne, hsub, rfl⟩

open Classical in
theorem mem_dualCell_faces_iff_of_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ A.faces) {u : Finset E}
    (hu : u ∈ (barycentricSubdivision A).faces) :
    u ∈ (dualCell K e (hAK he)).faces ↔ u ∈ (dualCell A e he).faces := by
  obtain ⟨d, hd, hne, rfl⟩ := hu
  rw [mem_dualCell_faces_iff_of_flag (hAK he) (hd.of_le hAK) hne,
    mem_dualCell_faces_iff_of_flag he hd hne]

open Classical in
theorem dualCell_space_inter_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ A.faces) :
    (dualCell K e (hAK he)).space ∩ A.space = (dualCell A e he).space := by
  apply Subset.antisymm
  · rintro x ⟨hxD, hxA⟩
    have hxAb : x ∈ (barycentricSubdivision A).space :=
      (barycentricSubdivision_isSubdivision A).space_eq.symm ▸ hxA
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (barycentricSubdivision A) hxAb
    have huD := mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K (hAK he))
      (barycentricSubdivision_faces_subset hAK hu) hxu hxD
    exact (dualCell A e he).convexHull_subset_space
      ((mem_dualCell_faces_iff_of_subcomplex K A hAK he hu).mp huD)
      (openSimplex_subset_convexHull u hxu)
  · intro x hx
    refine ⟨space_mono_of_faces_subset (dualCell_faces_subset_of_subcomplex K A hAK he) hx, ?_⟩
    exact (barycentricSubdivision_isSubdivision A).space_eq ▸
      space_mono_of_faces_subset (dualCell_faces_subset A he) hx

open Classical in
theorem graphDualCell_space_eq_inter
    (K L : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∈ K.faces) :
    (graphDualCell K L v).space =
      (derivedNeighborhood K L).space ∩ closedStar (barycentricSubdivision K) v := by
  have h := restrict_space_eq_inter_of_faces_subset (secondDerived K)
    (derivedNeighborhood K L) (barycentricSubdivision (dualCell K {v} hv))
    (derivedNeighborhood_faces_subset K L)
    (barycentricSubdivision_faces_subset (dualCell_faces_subset K hv))
  rw [(barycentricSubdivision_isSubdivision (dualCell K {v} hv)).space_eq] at h
  simpa only [graphDualCell, closedStar_barycentricSubdivision_eq_dualCell K hv] using h

open Classical in
theorem graphDualCell_space_inter_subcomplex
    (K A L : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {v : E} (hv : {v} ∈ A.faces) :
    (graphDualCell K L v).space ∩ A.space = (graphDualCell A L v).space := by
  rw [graphDualCell_space_eq_inter K L (hAK hv), graphDualCell_space_eq_inter A L hv]
  calc
    _ = ((derivedNeighborhood K L).space ∩ A.space) ∩
        (closedStar (barycentricSubdivision K) v ∩ A.space) := by
      ext x
      simp only [mem_inter_iff]
      tauto
    _ = _ := by
      rw [derivedNeighborhood_space_inter_subcomplex K A L hAK,
        closedStar_barycentricSubdivision_inter_space_eq hAK hv]

open Classical in
theorem splittingDisk_space_inter_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ A.faces) :
    (splittingDisk K e (hAK he)).space ∩ A.space = (splittingDisk A e he).space := by
  calc
    _ = (splittingDisk K e (hAK he)).space ∩ (dualCell A e he).space := by
      rw [← dualCell_space_inter_subcomplex K A hAK he]
      ext x
      exact ⟨fun h => ⟨h.1, splittingDisk_space_subset_dualCell K (hAK he) h.1, h.2⟩,
        fun h => ⟨h.1, h.2.2⟩⟩
    _ = _ := by
      rw [splittingDisk_space K (hAK he), splittingDisk_space A he]
      exact closedStar_barycentricSubdivision_inter_space_eq
        (dualCell_faces_subset_of_subcomplex K A hAK he) (singleton_centroid_mem_dualCell A he)

end DifferentialGeometry.Topology.PiecewiseLinear
