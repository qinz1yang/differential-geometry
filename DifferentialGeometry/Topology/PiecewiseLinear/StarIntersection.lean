/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem closedStar_barycentricSubdivision_inter_space_eq
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {x : E} (hxL : {x} ∈ L.faces) :
    closedStar (barycentricSubdivision K) x ∩ L.space =
      closedStar (barycentricSubdivision L) x := by
  classical
  have hLK : (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces :=
    barycentricSubdivision_faces_subset hL
  have hxK : {x} ∈ K.faces := hL hxL
  have hxKb : {x} ∈ (barycentricSubdivision K).faces :=
    (barycentricSubdivision_isSubdivision K).singleton_mem hxK
  apply Subset.antisymm
  · rintro y ⟨hyK, hyL⟩
    obtain ⟨u, ⟨hu, hxu⟩, hyu⟩ := mem_iUnion₂.mp hyK
    have hxu' : x ∈ u :=
      mem_of_mem_convexHull_of_singleton_mem (barycentricSubdivision K) hxKb hu hxu
    have hyLb : y ∈ (barycentricSubdivision L).space := by
      rw [(barycentricSubdivision_isSubdivision L).space_eq]
      exact hyL
    obtain ⟨v, hv, hyv⟩ := (barycentricSubdivision L).mem_space_iff.mp hyLb
    have hyuv : y ∈ convexHull ℝ (((u ∩ v : Finset E) : Set E)) :=
      by simpa only [Finset.coe_inter] using
        (barycentricSubdivision K).inter_subset_convexHull hu (hLK hv) ⟨hyu, hyv⟩
    have huvne : (u ∩ v).Nonempty := nonempty_of_mem_convexHull hyuv
    have huvL : u ∩ v ∈ (barycentricSubdivision L).faces :=
      (barycentricSubdivision L).down_closed hv Finset.inter_subset_right huvne
    obtain ⟨D, hD, hDne, huvD⟩ := huvL
    have hxs : ∀ s ∈ D, {x} ⊆ s := by
      intro s hs
      have hcsuv : s.centroid ℝ id ∈ u ∩ v := by
        rw [huvD]
        exact Finset.mem_image_of_mem _ hs
      have hcomp := subset_or_subset_of_centroid_mem_face K hxK (hL (hD.mem_faces hs)) hu
        (by simpa only [Finset.centroid_singleton, id_eq] using hxu')
        (Finset.mem_inter.mp hcsuv).1
      rcases hcomp with h | h
      · exact h
      · rcases Finset.subset_singleton_iff.mp h with hempty | heq
        · exact ((L.nonempty_of_mem_faces (hD.mem_faces hs)).ne_empty hempty).elim
        · rw [heq]
    have hins : insert x (u ∩ v) ∈ (barycentricSubdivision L).faces := by
      have hflag := hD.insert_of_subset hxL hxs
      have hface : (insert {x} D).image (fun s => s.centroid ℝ id) ∈
          (barycentricSubdivision L).faces :=
        ⟨insert {x} D, hflag, Finset.insert_nonempty _ _, rfl⟩
      simpa only [Finset.image_insert, Finset.centroid_singleton, id_eq, ← huvD] using hface
    exact mem_iUnion₂.mpr ⟨insert x (u ∩ v),
      ⟨hins, subset_convexHull ℝ _ (Finset.mem_insert_self _ _)⟩,
      convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hyuv⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · obtain ⟨u, ⟨hu, hxu⟩, hyu⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨u, ⟨hLK hu, hxu⟩, hyu⟩
    · rw [← (barycentricSubdivision_isSubdivision L).space_eq]
      exact closedStar_subset_space (barycentricSubdivision L) x hy

end DifferentialGeometry.Topology.PiecewiseLinear
