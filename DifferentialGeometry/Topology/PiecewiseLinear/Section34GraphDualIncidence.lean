/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SubdivisionCarriers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem graphDualCell_inter_convexHull_nonempty_iff_of_subdivision
    {K K' : Geometry.SimplicialComplex ℝ E} (hsub : IsSubdivision K' K)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K'.faces)
    {v : E} (hv : {v} ∈ L.faces) {t : Finset E} (ht : t ∈ K.faces) :
    ((graphDualCell K' L v).space ∩ convexHull ℝ (t : Set E)).Nonempty ↔
      v ∈ convexHull ℝ (t : Set E) := by
  classical
  constructor
  · rintro ⟨x, hxD, hxt⟩
    obtain ⟨s, hs, hxs, hst⟩ := hsub.exists_face_subset_of_mem ht hxt
    have hxdual := graphDualCell_space_subset_closedStar K' L v hxD
    rw [closedStar_barycentricSubdivision_eq_dualCell K' (hL hv)] at hxdual
    have hvs := subset_of_mem_dualCell_of_mem_convexHull K' (hL hv) hs hxdual hxs
    exact hst (subset_convexHull ℝ _ (Finset.singleton_subset_iff.mp hvs))
  · intro hvt
    exact ⟨v, mem_graphDualCell_space_of_singleton_mem K' L hL hv, hvt⟩

theorem image_graphDualCell_inter_simplexBody_nonempty_iff
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn E 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ 𝒦'.complex.faces)
    {v : E} (hv : {v} ∈ L.faces) {t : Finset E} (ht : t ∈ 𝒦.complex.faces) :
    (𝒦'.map '' (graphDualCell 𝒦'.complex L v).space ∩ simplexBody 𝒦 t).Nonempty ↔
      v ∈ convexHull ℝ (t : Set E) := by
  classical
  constructor
  · rintro ⟨z, ⟨x, hx, hxz⟩, y, hy, hyz⟩
    have hxK : x ∈ 𝒦.complex.space := by
      rw [← hsub.space_eq]
      exact derivedNeighborhood_space_subset 𝒦'.complex L
        (graphDualCell_space_subset 𝒦'.complex L v hx)
    have heq : x = y := 𝒦.bijOn.injOn hxK (𝒦.complex.convexHull_subset_space ht hy)
      (by simpa only [hmap] using hxz.trans hyz.symm)
    apply (graphDualCell_inter_convexHull_nonempty_iff_of_subdivision hsub L hL hv ht).mp
    exact ⟨x, hx, heq.symm ▸ hy⟩
  · intro hvt
    refine ⟨𝒦'.map v, mem_image_of_mem _
      (mem_graphDualCell_space_of_singleton_mem 𝒦'.complex L hL hv), v, hvt, ?_⟩
    rw [hmap]

theorem image_graphDualCell_subset_section34CarrierSupport
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (L : Geometry.SimplicialComplex ℝ Ea) {v : Ea} (hv : {v} ∈ 𝒦'.complex.faces)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (hvt : v ∈ convexHull ℝ (t : Set Ea)) :
    𝒦'.map '' (graphDualCell 𝒦'.complex L v).space ⊆ Section34CarrierSupport 𝒦 t := by
  classical
  apply Subset.trans (b := Section34CarrierSupport 𝒦' {v})
  · rintro y ⟨x, hx, rfl⟩
    have hxK := derivedNeighborhood_space_subset 𝒦'.complex L
      (graphDualCell_space_subset 𝒦'.complex L v hx)
    obtain ⟨s, hs, hxs⟩ := 𝒦'.complex.mem_space_iff.mp hxK
    have hxdual := graphDualCell_space_subset_closedStar 𝒦'.complex L v hx
    rw [closedStar_barycentricSubdivision_eq_dualCell 𝒦'.complex hv] at hxdual
    have hvs := subset_of_mem_dualCell_of_mem_convexHull 𝒦'.complex hv hs hxdual hxs
    exact mem_iUnion₂.mpr ⟨v, by simp, mem_iUnion₂.mpr
      ⟨s, ⟨hs, Finset.singleton_subset_iff.mp hvs⟩, x, hxs, rfl⟩⟩
  · apply section34CarrierSupport_subset_of_subdivision hsub hmap ht
    simpa using hvt

end DifferentialGeometry.Topology.PiecewiseLinear
