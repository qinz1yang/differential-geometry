/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

theorem mem_restrict_preimage_graphSkeletonSpace_iff
    (T : LocallyFinitePLPieceIn E 3 X U) {s : Finset E} :
    s ∈ (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)).faces ↔
      s ∈ T.complex.faces ∧ s.card ≤ 2 := by
  constructor
  · rintro ⟨hs, hsub⟩
    have hne := T.complex.nonempty_of_mem_faces hs
    have hx := hsub (s.centroid_mem_convexHull hne)
    obtain ⟨e, ⟨he, hcard⟩, y, hy, heq⟩ := mem_iUnion₂.mp hx
    have hyx : y = s.centroid ℝ id := T.bijOn.injOn
      (T.complex.convexHull_subset_space he hy)
      (T.complex.convexHull_subset_space hs (s.centroid_mem_convexHull hne)) heq
    rw [hyx] at hy
    exact ⟨hs, (Finset.card_le_card (face_subset_of_mem_openSimplex_of_mem_convexHull
      T.complex hs he (centroid_mem_openSimplex hne) hy)).trans hcard⟩
  · rintro ⟨hs, hcard⟩
    exact ⟨hs, fun x hx => mem_iUnion₂.mpr ⟨s, ⟨hs, hcard⟩, x, hx, rfl⟩⟩

theorem image_restrict_preimage_graphSkeletonSpace
    (T : LocallyFinitePLPieceIn E 3 X U) :
    T.map '' (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)).space =
      graphSkeletonSpace T := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact restrict_space_subset T.complex _ hx
  · intro y hy
    obtain ⟨s, ⟨hs, hcard⟩, x, hx, rfl⟩ := mem_iUnion₂.mp hy
    exact ⟨x, (restrict T.complex _).convexHull_subset_space
      ((mem_restrict_preimage_graphSkeletonSpace_iff T).mpr ⟨hs, hcard⟩) hx, rfl⟩

theorem restrict_preimage_graphSkeletonSpace_space
    (T : LocallyFinitePLPieceIn E 3 X U) :
    (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)).space =
      T.complex.space ∩ T.map ⁻¹' graphSkeletonSpace T := by
  apply Subset.antisymm
  · exact subset_inter (space_mono_of_faces_subset (restrict_faces_subset T.complex _))
      (restrict_space_subset T.complex _)
  · rintro x ⟨hx, hgraph⟩
    obtain ⟨y, hy, heq⟩ := (image_restrict_preimage_graphSkeletonSpace T).symm.subset hgraph
    have hyT := space_mono_of_faces_subset (restrict_faces_subset T.complex _) hy
    exact (T.bijOn.injOn hyT hx heq) ▸ hy

theorem isSubdivision_restrict_preimage_graphSkeletonSpace
    {T T' : LocallyFinitePLPieceIn E 3 X U}
    (hsub : IsSubdivision T'.complex T.complex) (hmap : T'.map = T.map) :
    IsSubdivision (restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T))
      (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)) := by
  have heq : restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T) =
      restrict T'.complex (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)).space := by
    rw [restrict_preimage_graphSkeletonSpace_space, hmap]
    ext s
    constructor
    · rintro ⟨hs, hsg⟩
      exact ⟨hs, subset_inter
        ((T'.complex.convexHull_subset_space hs).trans hsub.space_eq.subset) hsg⟩
    · rintro ⟨hs, hsg⟩
      exact ⟨hs, hsg.trans inter_subset_right⟩
  rw [heq]
  exact hsub.restrict _ (restrict_faces_subset T.complex _)

end DifferentialGeometry.Topology.PiecewiseLinear
