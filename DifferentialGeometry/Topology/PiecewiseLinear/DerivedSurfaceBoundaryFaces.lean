/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCrossingArcs
import DifferentialGeometry.Topology.PiecewiseLinear.StarSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem mem_boundaryComplex_of_comparable_face_of_local_reading
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces] (hΓR : Γ.faces ⊆ R.faces)
    {s t : Finset E} (hs : s ∈ Γ.faces) (ht : t ∈ Γ.faces) (hcomp : s ⊆ t ∨ t ⊆ s)
    {P W : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hPR : (PiecewiseLinear.restrict R P).space = P)
    (hbd : ∀ x ∈ R.space ∩ W, x ∈ q '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hstar : (⋃ v ∈ s, closedStar R v) ⊆ W) :
    t ∈ (boundaryComplex 2 (PiecewiseLinear.restrict R P)).faces := by
  let A := PiecewiseLinear.restrict R P
  let _ : Finite A.faces := (restrict_faces_finite R _).to_subtype
  have hAbd := hq.image_stdSimplexBoundary_eq_boundaryComplex A hPR
  have hcommon : ∃ v, v ∈ s ∧ v ∈ t := by
    rcases hcomp with h | h
    · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hs
      exact ⟨v, hv, h hv⟩
    · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces ht
      exact ⟨v, h hv, hv⟩
  obtain ⟨v, hvs, hvt⟩ := hcommon
  have hcentroidHull : t.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    t.centroid_mem_convexHull (Γ.nonempty_of_mem_faces ht)
  have hcentroidW : t.centroid ℝ id ∈ W :=
    hstar (mem_iUnion₂.mpr ⟨v, hvs, mem_iUnion₂.mpr
      ⟨t, ⟨hΓR ht, subset_convexHull ℝ _ hvt⟩, hcentroidHull⟩⟩)
  apply mem_faces_of_mem_openSimplex_of_mem_space
    ((boundaryComplex_faces_subset 2 A).trans (restrict_faces_subset R _)) (hΓR ht)
    (centroid_mem_openSimplex_of_mem_faces R t (hΓR ht))
  rw [← hAbd]
  exact (hbd _ ⟨R.convexHull_subset_space (hΓR ht) hcentroidHull, hcentroidW⟩).mpr
    (Γ.convexHull_subset_space ht hcentroidHull)

end DifferentialGeometry.Topology.PiecewiseLinear
