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
theorem dualCell_space_inter_iUnion_closedStar_eq_upperLink
    (A : Geometry.SimplicialComplex ℝ E) {e : Finset E} (he : e ∈ A.faces) :
    (dualCell A e he).space ∩
      (⋃ q ∈ A.vertices \ (e : Set E), closedStar (barycentricSubdivision A) q) =
        (upperLink A e).space := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hxD, hxU⟩
    obtain ⟨q, ⟨hq, hqe⟩, hxq⟩ := mem_iUnion₂.mp hxU
    rw [closedStar_barycentricSubdivision_eq_dualCell A hq] at hxq
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (dualCell A e he) hxD
    have huq := mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset A hq)
      (dualCell_faces_subset A he hu) hxu hxq
    obtain ⟨d, hd, hne, hsub, rfl⟩ := (mem_dualCell_faces_iff A he).mp hu
    have hqsub := (mem_dualCell_faces_iff_of_flag hq hd hne).mp huq
    apply (upperLink A e).convexHull_subset_space
      ((mem_upperLink_faces_iff A e).mpr ⟨d, hd, hne, ?_, rfl⟩)
      (openSimplex_subset_convexHull _ hxu)
    intro s hs
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub s hs, ?_⟩
    intro hes
    exact hqe (hes.symm ▸ Finset.singleton_subset_iff.mp (hqsub s hs))
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (upperLink A e).mem_space_iff.mp hx
    obtain ⟨d, hd, hne, hlt, rfl⟩ := (mem_upperLink_faces_iff A e).mp hu
    have hxD : x ∈ (dualCell A e he).space :=
      (dualCell A e he).convexHull_subset_space
        ((mem_dualCell_faces_iff_of_flag he hd hne).mpr fun s hs => (hlt s hs).subset) hxu
    obtain ⟨s, hs, hbot⟩ := hd.exists_bot hne
    obtain ⟨q, hqs, hqe⟩ := Finset.exists_of_ssubset (hlt s hs)
    have hq : {q} ∈ A.faces := A.down_closed (hd.mem_faces hs)
      (Finset.singleton_subset_iff.mpr hqs) (Finset.singleton_nonempty q)
    refine ⟨hxD, mem_iUnion₂.mpr ⟨q, ⟨hq, hqe⟩, ?_⟩⟩
    rw [closedStar_barycentricSubdivision_eq_dualCell A hq]
    apply (dualCell A {q} hq).convexHull_subset_space
      ((mem_dualCell_faces_iff_of_flag hq hd hne).mpr ?_) hxu
    exact fun t ht => Finset.singleton_subset_iff.mpr (hbot t ht hqs)

open Classical in
theorem dualCell_space_inter_iUnion_singleton_eq_upperLink
    (A : Geometry.SimplicialComplex ℝ E) {p : E} (hp : {p} ∈ A.faces) :
    (dualCell A {p} hp).space ∩
      (⋃ (q : A.vertices) (_ : (q : E) ≠ p), (dualCell A {q.1} q.2).space) =
        (upperLink A {p}).space := by
  classical
  have hU : (⋃ (q : A.vertices) (_ : (q : E) ≠ p), (dualCell A {q.1} q.2).space) =
      ⋃ q ∈ A.vertices \ ({p} : Set E), closedStar (barycentricSubdivision A) q := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨q, hqp, hxq⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion₂.mpr ⟨q.1, ⟨q.2, hqp⟩, ?_⟩
      rwa [closedStar_barycentricSubdivision_eq_dualCell A q.2]
    · intro x hx
      obtain ⟨q, ⟨hq, hqp⟩, hxq⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion₂.mpr ⟨⟨q, hq⟩, hqp, ?_⟩
      rwa [closedStar_barycentricSubdivision_eq_dualCell A hq] at hxq
  rw [hU]
  simpa only [Finset.coe_singleton] using dualCell_space_inter_iUnion_closedStar_eq_upperLink A hp

end DifferentialGeometry.Topology.PiecewiseLinear
