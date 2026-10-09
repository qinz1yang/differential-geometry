/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhood_restrict_core_eq (K S L : Geometry.SimplicialComplex ℝ E)
    (hS : S.faces ⊆ K.faces) (hL : L.faces ⊆ K.faces) :
    derivedNeighborhood S (restrict L S.space) = derivedNeighborhood S L := by
  ext u
  constructor
  · intro hu
    exact derivedNeighborhood_faces_mono Subset.rfl (restrict_faces_subset L S.space) hu
  · rintro ⟨d, hd, hne, hmeet, rfl⟩
    refine ⟨d, hd, hne, ?_, rfl⟩
    intro e he
    obtain ⟨s, hs, hse⟩ := hmeet e he
    have hcent : s.centroid ℝ id ∈ S.space := by
      rw [← (barycentricSubdivision_isSubdivision S).space_eq]
      exact (barycentricSubdivision S).convexHull_subset_space (hd.mem_faces he)
        (subset_convexHull ℝ _ hse)
    have hsS : s ∈ S.faces := mem_faces_of_mem_openSimplex_of_mem_space hS (hL hs)
      (centroid_mem_openSimplex (L.nonempty_of_mem_faces hs)) hcent
    exact ⟨s, ⟨hs, S.convexHull_subset_space hsS⟩, hse⟩

theorem iUnion_restrict_space_of_faces_iUnion {ι : Sort*}
    (K L : Geometry.SimplicialComplex ℝ E) (A : ι → Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hA : K.faces = ⋃ i, (A i).faces) :
    (⋃ i, (restrict L (A i).space).space) = L.space := by
  apply Subset.antisymm
  · exact iUnion_subset fun i => space_mono_of_faces_subset (restrict_faces_subset L _)
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    obtain ⟨i, hsi⟩ := mem_iUnion.mp (hA ▸ hL hs)
    exact mem_iUnion.mpr ⟨i, (restrict L (A i).space).convexHull_subset_space
      ⟨hs, (A i).convexHull_subset_space hsi⟩ hxs⟩

open Classical in
theorem iUnion_derivedNeighborhood_restrict_space {ι : Sort*}
    (K L : Geometry.SimplicialComplex ℝ E) (A : ι → Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hA : K.faces = ⋃ i, (A i).faces) :
    (⋃ i, (derivedNeighborhood (A i) (restrict L (A i).space)).space) =
      (derivedNeighborhood K L).space := by
  have hAK (i : ι) : (A i).faces ⊆ K.faces := by
    intro s hs
    rw [hA]
    exact mem_iUnion.mpr ⟨i, hs⟩
  simp_rw [derivedNeighborhood_restrict_core_eq K _ L (hAK _) hL]
  apply Subset.antisymm
  · exact iUnion_subset fun i => space_mono_of_faces_subset
      (derivedNeighborhood_faces_mono (hAK i) Subset.rfl)
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp (derivedNeighborhood_space_subset K L hx)
    obtain ⟨i, hsi⟩ := mem_iUnion.mp (hA ▸ hs)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [← derivedNeighborhood_space_inter_subcomplex K (A i) L (hAK i)]
    exact ⟨hx, (A i).convexHull_subset_space hsi hxs⟩

open Classical in
theorem derivedNeighborhood_restrict_space_mem_nhdsWithin
    (K S L : Geometry.SimplicialComplex ℝ E) (hS : S.faces ⊆ K.faces)
    (hL : L.faces ⊆ K.faces) {x : E} (hx : S.space ∈ 𝓝[K.space] x) :
    (derivedNeighborhood S (restrict L S.space)).space ∈
      𝓝[(derivedNeighborhood K L).space] x := by
  rw [derivedNeighborhood_restrict_core_eq K S L hS hL,
    ← derivedNeighborhood_space_inter_subcomplex K S L hS]
  exact Filter.inter_mem self_mem_nhdsWithin
    (nhdsWithin_mono x (derivedNeighborhood_space_subset K L) hx)

end DifferentialGeometry.Topology.PiecewiseLinear
