/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PreimageBoundaryRelative

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem boundary_preimage_ne_singleton_of_transverse_facet
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (φ : E → F) {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    {s : Finset E} (hs : s ∈ (boundaryComplex (m + 1) K).faces) (hcard : s.card = m + 1)
    {z : E} (hz : z ∈ openSimplex s) (hind : AffineIndependent ℝ (fun v : s => φ v))
    (htrans : ∀ t ∈ L.faces,
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤) :
    (boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space ≠ {z} := by
  intro htrace
  have hsK := boundaryComplex_faces_subset (m + 1) K hs
  let B := simplexComplex s (K.indep hsK)
  have hBd : B.faces ⊆ (boundaryComplex (m + 1) K).faces := fun u hu =>
    (boundaryComplex (m + 1) K).down_closed hs hu.2 hu.1
  have hBK : B.faces ⊆ K.faces := hBd.trans (boundaryComplex_faces_subset (m + 1) K)
  have hgood : ∀ u ∈ B.faces, AffineIndependent ℝ (fun v : u => φ v) ∧
      ∀ t ∈ L.faces,
        (convexHull ℝ (u.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
          vectorSpan ℝ (u.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤ := by
    intro u hu
    have hdata := (affineIndependent_image_iff s φ).mp hind
    have huinj : InjOn φ (u : Set E) := hdata.1.mono (Finset.coe_subset.mpr hu.2)
    refine ⟨(affineIndependent_image_iff u φ).mpr ⟨huinj,
      affineIndependent_of_subset hdata.2 (Finset.image_mono φ hu.2)⟩, ?_⟩
    intro t ht hinter
    obtain ⟨y, hyu, hyt⟩ := hinter
    rw [← image_convexHull_simplicialMap K φ (hBK hu) huinj] at hyu
    obtain ⟨w, hwu, hw⟩ := hyu
    have hwz : w = z := htrace.subset
      ⟨(boundaryComplex (m + 1) K).convexHull_subset_space (hBd hu) hwu,
        by change simplicialMap K φ w ∈ L.space; rw [hw]; exact L.convexHull_subset_space ht hyt⟩
    have hsu : s ⊆ u := face_subset_of_mem_openSimplex_of_mem_convexHull K hsK (hBK hu)
      hz (hwz ▸ hwu)
    have hueq : u = s := Finset.Subset.antisymm hu.2 hsu
    subst u
    exact htrans t ht ⟨y, by rw [← hw]; exact simplicialMap_mem_convexHull_image K φ hsK hwu, hyt⟩
  have hout : ∀ u ∈ (boundaryComplex (m + 1) K).faces, u ∉ B.faces →
      MapsTo (simplicialMap K φ) (convexHull ℝ (u : Set E)) L.spaceᶜ := by
    intro u hu huB w hw hwL
    have hwz : w = z := htrace.subset
      ⟨(boundaryComplex (m + 1) K).convexHull_subset_space hu hw, hwL⟩
    have hsu : s ⊆ u := face_subset_of_mem_openSimplex_of_mem_convexHull K hsK
      (boundaryComplex_faces_subset (m + 1) K hu) hz (hwz ▸ hw)
    obtain ⟨w, _, huw, hwcard, _⟩ := hu.2
    have hucard := (Finset.card_le_card huw).trans hwcard
    have hueq : u = s := (Finset.eq_of_subset_of_card_le hsu (by omega)).symm
    exact huB (hueq.symm ▸ show s ∈ B.faces from ⟨K.nonempty_of_mem_faces hsK, Finset.Subset.refl
        s⟩)
  have heven := even_ncard_boundary_preimage_of_transverse_subcomplex K B L hBK φ
    hK hL hdim hgood hout
  rw [htrace, Set.ncard_singleton] at heven
  exact (by decide : ¬Even (1 : ℕ)) heven

open Classical in
theorem boundary_preimage_ne_singleton_of_transverse_openSimplex
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (φ : E → F) {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    {s : Finset E} (hs : s ∈ (boundaryComplex (m + 1) K).faces) (hscard : s.card = m + 1)
    {t : Finset F} (ht : t ∈ L.faces) (htcard : t.card = n + 2)
    {z : E} (hz : z ∈ openSimplex s) (hφz : simplicialMap K φ z ∈ openSimplex t)
    (hind : AffineIndependent ℝ (fun v : s => φ v))
    (hspan : vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤) :
    (boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space ≠ {z} := by
  intro htrace
  apply boundary_preimage_ne_singleton_of_transverse_facet K L φ hK hL hdim hs hscard hz hind
    (fun u hu hinter => ?_) htrace
  obtain ⟨y, hys, hyu⟩ := hinter
  rw [← image_convexHull_simplicialMap K φ (boundaryComplex_faces_subset (m + 1) K hs)
    ((affineIndependent_image_iff s φ).mp hind).1] at hys
  obtain ⟨w, hws, hw⟩ := hys
  have hwz : w = z := htrace.subset
    ⟨(boundaryComplex (m + 1) K).convexHull_subset_space hs hws,
      by change simplicialMap K φ w ∈ L.space; rw [hw]; exact L.convexHull_subset_space hu hyu⟩
  have hzu : simplicialMap K φ z ∈ convexHull ℝ (u : Set F) := by
    rw [← hwz, hw]
    exact hyu
  have htu := face_subset_of_mem_openSimplex_of_mem_convexHull L ht hu hφz hzu
  have hucard := hL.card_le L hu
  have hut : u = t := (Finset.eq_of_subset_of_card_le htu (by omega)).symm
  simpa only [hut] using hspan

end DifferentialGeometry.Topology.PiecewiseLinear
