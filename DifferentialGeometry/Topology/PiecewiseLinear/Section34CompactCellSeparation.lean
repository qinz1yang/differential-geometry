/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem closedStar_barycentricSubdivision_inter_convexHull_eq_empty
    {M : Geometry.SimplicialComplex ℝ E} {u : E} (hu : {u} ∈ M.faces) {s : Finset E}
    (hs : s ∈ M.faces) (hus : u ∉ s) :
    closedStar (barycentricSubdivision M) u ∩ convexHull ℝ (s : Set E) = ∅ := by
  classical
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hxstar, hxs⟩
  obtain ⟨σ, ⟨hσ, huσ⟩, hxσ⟩ := mem_iUnion₂.mp hxstar
  have hbu : ({u} : Finset E).centroid ℝ id = u := by
    rw [Finset.centroid_singleton]
    rfl
  have hu1 : {u} ∈ (barycentricSubdivision M).faces := by
    have h := singleton_centroid_mem_barycentricSubdivision M hu
    rwa [hbu] at h
  have huσ' : u ∈ σ := by
    have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull (barycentricSubdivision M)
      hu1 hσ (centroid_mem_openSimplex (Finset.singleton_nonempty u) |> fun h => by
        rwa [hbu] at h) huσ
    exact hsub (Finset.mem_singleton_self u)
  set S := restrict M (convexHull ℝ (s : Set E))
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset M _
  have hxS : x ∈ (barycentricSubdivision S).space := by
    rw [(barycentricSubdivision_isSubdivision S).space_eq, restrict_convexHull_space hs]
    exact hxs
  have hxM : x ∈ (barycentricSubdivision M).space :=
    (barycentricSubdivision M).convexHull_subset_space hσ hxσ
  obtain ⟨τ, hτ, hxτ⟩ := exists_face_mem_openSimplex (barycentricSubdivision M) hxM
  have hτσ : τ ⊆ σ :=
    face_subset_of_mem_openSimplex_of_mem_convexHull (barycentricSubdivision M) hτ hσ hxτ hxσ
  have hτS : τ ∈ (barycentricSubdivision S).faces :=
    mem_faces_of_mem_openSimplex_of_mem_space (barycentricSubdivision_faces_subset hSM) hτ hxτ
      hxS
  obtain ⟨d, hd, -, rfl⟩ := hσ
  obtain ⟨ρu, hρu, hρuu⟩ := Finset.mem_image.mp huσ'
  have hρu1 : ρu = {u} := injOn_faces_of_mem_openSimplex M (centroid_mem_openSimplex_of_mem_faces M)
    (hd.1 ρu hρu) hu (hρuu.trans hbu.symm)
  obtain ⟨d', hd', hd'ne, rfl⟩ := hτS
  obtain ⟨ρ', hρ'⟩ := hd'ne
  have hpσ := hτσ (Finset.mem_image_of_mem (fun e => e.centroid ℝ id) hρ')
  obtain ⟨ρ, hρ, hρρ'⟩ := Finset.mem_image.mp hpσ
  have hρρ'eq : ρ = ρ' := injOn_faces_of_mem_openSimplex M
    (centroid_mem_openSimplex_of_mem_faces M) (hd.1 ρ hρ) (hSM (hd'.1 ρ' hρ')) hρρ'
  have huρ : u ∈ ρ := by
    rcases hd.2 ρu hρu ρ hρ with h | h
    · rw [hρu1] at h
      exact h (Finset.mem_singleton_self u)
    · rw [hρu1] at h
      have hne := M.nonempty_of_mem_faces (hd.1 ρ hρ)
      obtain ⟨p, hp⟩ := hne
      have hpu := Finset.mem_singleton.mp (h hp)
      rw [← hpu]
      exact hp
  have hρ's : ρ' ⊆ s := by
    have hρ'S := hd'.1 ρ' hρ'
    have hne := S.nonempty_of_mem_faces hρ'S
    exact face_subset_of_mem_openSimplex_of_mem_convexHull M (hSM hρ'S) hs
      (centroid_mem_openSimplex hne) (hρ'S.2 (openSimplex_subset_convexHull ρ'
        (centroid_mem_openSimplex hne)))
  exact hus (hρ's (hρρ'eq ▸ huρ))

open Classical in
theorem graphDualCell_space_inter_convexHull_eq_empty {M : Geometry.SimplicialComplex ℝ E}
    (L : Geometry.SimplicialComplex ℝ E) {u : E} (hu : {u} ∈ M.faces) {s : Finset E}
    (hs : s ∈ M.faces) (hus : u ∉ s) :
    (graphDualCell M L u).space ∩ convexHull ℝ (s : Set E) = ∅ :=
  eq_empty_of_subset_empty ((inter_subset_inter_left _
    (graphDualCell_space_subset_closedStar M L u)).trans
      (closedStar_barycentricSubdivision_inter_convexHull_eq_empty hu hs hus).subset)

open Classical in
theorem notMem_graphDualCell_space_of_ne {M : Geometry.SimplicialComplex ℝ E}
    (L : Geometry.SimplicialComplex ℝ E) {u w : E} (hu : {u} ∈ M.faces) (hw : {w} ∈ M.faces)
    (huw : u ≠ w) : w ∉ (graphDualCell M L u).space := by
  intro hwu
  have h := graphDualCell_space_inter_convexHull_eq_empty L hu hw
    (fun h => huw (Finset.mem_singleton.mp h))
  have hw' : w ∈ convexHull ℝ (({w} : Finset E) : Set E) := subset_convexHull ℝ _ (by simp)
  exact (eq_empty_iff_forall_notMem.mp h) w ⟨hwu, hw'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
