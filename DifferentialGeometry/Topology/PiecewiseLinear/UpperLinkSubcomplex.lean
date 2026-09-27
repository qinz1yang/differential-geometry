/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem upperLink_space_inter_subcomplex (K L : Geometry.SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) (e : Finset E) :
    (upperLink K e).space ∩ L.space = (upperLink L e).space := by
  have hLbK : (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces :=
    barycentricSubdivision_faces_subset hLK
  apply Subset.antisymm
  · rintro x ⟨hxU, hxL⟩
    obtain ⟨u, hu, hxu⟩ := (upperLink K e).mem_space_iff.mp hxU
    have hxLb : x ∈ (barycentricSubdivision L).space := by
      rwa [(barycentricSubdivision_isSubdivision L).space_eq]
    obtain ⟨v, hv, hxv⟩ := (barycentricSubdivision L).mem_space_iff.mp hxLb
    have hxuv : x ∈ convexHull ℝ ((u ∩ v : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using
        (barycentricSubdivision K).inter_subset_convexHull
          (upperLink_faces_subset K e hu) (hLbK hv) ⟨hxu, hxv⟩
    have huv : (u ∩ v).Nonempty := nonempty_of_mem_convexHull hxuv
    have hwU := (upperLink K e).down_closed hu Finset.inter_subset_left huv
    have hwL := (barycentricSubdivision L).down_closed hv Finset.inter_subset_right huv
    obtain ⟨d, hd, hne, hlt, hdw⟩ := hwU
    have hdL : IsFlag L d := by
      refine ⟨fun s hs => ?_, hd.2⟩
      apply mem_faces_of_mem_openSimplex_of_mem_space hLK (hd.mem_faces hs)
        (centroid_mem_openSimplex_of_mem_faces K s (hd.mem_faces hs))
      rw [← (barycentricSubdivision_isSubdivision L).space_eq]
      exact (barycentricSubdivision L).subset_space hwL
        (hdw.symm ▸ Finset.mem_image_of_mem (fun s : Finset E => s.centroid ℝ id) hs)
    exact (upperLink L e).convexHull_subset_space ⟨d, hdL, hne, hlt, hdw⟩ hxuv
  · intro x hx
    constructor
    · apply space_mono_of_faces_subset (K := upperLink K e) (L := upperLink L e) ?_ hx
      rintro u ⟨d, hd, hne, hlt, rfl⟩
      exact ⟨d, hd.of_le hLK, hne, hlt, rfl⟩
    · rw [← (barycentricSubdivision_isSubdivision L).space_eq]
      exact space_mono_of_faces_subset (upperLink_faces_subset L e) hx

end DifferentialGeometry.Topology.PiecewiseLinear
