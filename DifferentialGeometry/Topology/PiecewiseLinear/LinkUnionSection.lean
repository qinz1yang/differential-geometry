/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacetDirections

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem geometricLink_space_subset_union_of_faces_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (R M N : Geometry.SimplicialComplex ℝ E) {q : E}
    (hcover : ∀ s ∈ R.faces, s ∈ M.faces ∨ s ∈ N.faces) :
    (SimplicialComplex.geometricLink R {q}).space ⊆
      (SimplicialComplex.geometricLink M {q}).space ∪
        (SimplicialComplex.geometricLink N {q}).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ :=
    (SimplicialComplex.geometricLink R {q}).mem_space_iff.mp hx
  obtain ⟨hsne, hqs, hqsu⟩ :=
    (mem_geometricLink_faces_iff R).mp hs
  rcases hcover (insert q s) hqsu with hM | hN
  · exact Or.inl ((SimplicialComplex.geometricLink M {q}).convexHull_subset_space
      ((mem_geometricLink_faces_iff M).mpr ⟨hsne, hqs, hM⟩) hxs)
  · exact Or.inr ((SimplicialComplex.geometricLink N {q}).convexHull_subset_space
      ((mem_geometricLink_faces_iff N).mpr ⟨hsne, hqs, hN⟩) hxs)

theorem geometricLink_section_encard_le_two_of_faces_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (R M N : Geometry.SimplicialComplex ℝ E) {q : E}
    (hcover : ∀ s ∈ R.faces, s ∈ M.faces ∨ s ∈ N.faces)
    (f : E → ℝ)
    (hM : ((SimplicialComplex.geometricLink M {q}).space ∩
      {x | f x = f q}).Subsingleton)
    (hN : ((SimplicialComplex.geometricLink N {q}).space ∩
      {x | f x = f q}).Subsingleton) :
    ((SimplicialComplex.geometricLink R {q}).space ∩
      {x | f x = f q}).encard ≤ 2 := by
  let A := (SimplicialComplex.geometricLink M {q}).space ∩ {x | f x = f q}
  let B := (SimplicialComplex.geometricLink N {q}).space ∩ {x | f x = f q}
  have hsub : (SimplicialComplex.geometricLink R {q}).space ∩
      {x | f x = f q} ⊆ A ∪ B := by
    rintro x ⟨hx, hfx⟩
    rcases geometricLink_space_subset_union_of_faces_cover R M N hcover hx with hxM | hxN
    · exact Or.inl ⟨hxM, hfx⟩
    · exact Or.inr ⟨hxN, hfx⟩
  calc
    ((SimplicialComplex.geometricLink R {q}).space ∩
        {x | f x = f q}).encard ≤ (A ∪ B).encard := encard_mono hsub
    _ ≤ A.encard + B.encard := encard_union_le A B
    _ ≤ 1 + 1 := add_le_add
      (encard_le_one_iff_subsingleton.mpr hM)
      (encard_le_one_iff_subsingleton.mpr hN)
    _ = 2 := by norm_num

end DifferentialGeometry.Topology.PiecewiseLinear
