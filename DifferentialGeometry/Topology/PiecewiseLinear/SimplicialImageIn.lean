/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCollapse

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_subcomplex_space_eq_image_simplicialMap
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F) (φ : E → F)
    (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    ∃ A : Geometry.SimplicialComplex ℝ F, A.faces ⊆ L.faces ∧
      A.faces = simplicialImageFaces K φ ∧ A.space = simplicialMap K φ '' K.space := by
  have hsub : simplicialImageFaces K φ ⊆ L.faces := by
    rintro t ⟨s, hs, rfl⟩
    exact hφ s hs
  let A : Geometry.SimplicialComplex ℝ F :=
    { faces := simplicialImageFaces K φ
      isRelLowerSet_faces := simplicialImageFaces_isRelLowerSet K φ
      indep := fun hs => L.indep (hsub hs)
      inter_subset_convexHull := fun hs ht => L.inter_subset_convexHull (hsub hs) (hsub ht) }
  refine ⟨A, hsub, rfl, ?_⟩
  apply Subset.antisymm
  · intro y hy
    obtain ⟨t, ⟨s, hs, rfl⟩, hys⟩ := A.mem_space_iff.mp hy
    rw [← image_convexHull_simplicialMap_of_finiteDimensional K φ hs] at hys
    exact image_mono (K.convexHull_subset_space hs) hys
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    exact A.mem_space_iff.mpr
      ⟨s.image φ, ⟨s, hs, rfl⟩, simplicialMap_mem_convexHull_image K φ hs hxs⟩

open Classical in
theorem exists_finite_subcomplex_space_eq_image_simplicialMap
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) (φ : E → F)
    (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    ∃ A : Geometry.SimplicialComplex ℝ F, A.faces.Finite ∧ A.faces ⊆ L.faces ∧
      A.faces = simplicialImageFaces K φ ∧ A.space = simplicialMap K φ '' K.space := by
  obtain ⟨A, hAL, hfaces, hspace⟩ := exists_subcomplex_space_eq_image_simplicialMap K L φ hφ
  refine ⟨A, ?_, hAL, hfaces, hspace⟩
  rw [hfaces]
  exact ((Set.toFinite K.faces).image (fun s => s.image φ)).subset
    (fun t ⟨s, hs, hts⟩ => ⟨s, hs, hts.symm⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
