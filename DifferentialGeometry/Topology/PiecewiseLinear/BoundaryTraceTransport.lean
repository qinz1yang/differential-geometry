/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarTransport
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [dE : DecidableEq E] [dF : DecidableEq F]
  {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
  [Finite K.faces] [Finite L.faces] {φ : E → F} {ψ : F → E}

open Classical in
theorem IsGlueIso.image_boundaryComplex_inter_convexHull
    (h : IsGlueIso K L φ ψ) {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {t : Finset E} (ht : t ∈ K.faces) :
    simplicialMap K φ '' ((boundaryComplex (n + 1) K).space ∩ convexHull ℝ (t : Set E)) =
      (boundaryComplex (n + 1) L).space ∩ convexHull ℝ ((t.image φ : Finset F) : Set F) := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdF : dF = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dF
  have hf := h.isPLHomeomorphOn
  rw [hf.bijOn.injOn.image_inter (boundaryComplex_space_subset (n + 1) K)
    (K.convexHull_subset_space ht), h.image_convexHull ht,
    ← boundaryComplex_space_of_isPLHomeomorphOn K L hK hf]

open Classical in
theorem IsGlueIso.boundaryComplex_inter_convexHull_image
    (h : IsGlueIso K L φ ψ) {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {t s : Finset E} (ht : t ∈ K.faces) (hst : s ⊆ t) (htcard : 1 < t.card)
    (htrace : (boundaryComplex (n + 1) K).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)) :
    (boundaryComplex (n + 1) L).space ∩ convexHull ℝ ((t.image φ : Finset F) : Set F) =
      ⋃ v ∈ s.image φ, convexHull ℝ (((t.image φ).erase v : Finset F) : Set F) := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdF : dF = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dF
  rw [← h.image_boundaryComplex_inter_convexHull hK ht, htrace, image_iUnion]
  calc
    (⋃ v, simplicialMap K φ '' ⋃ (_ : v ∈ s), convexHull ℝ ((t.erase v : Finset E) : Set E)) =
        ⋃ v ∈ s, convexHull ℝ (((t.image φ).erase (φ v) : Finset F) : Set F) := by
      apply iUnion_congr
      intro v
      rw [image_iUnion]
      apply iUnion_congr
      intro hv
      have hvt : v ∈ t := hst hv
      have hne : (t.erase v).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_erase_of_mem hvt]
        omega)
      rw [h.image_convexHull (K.down_closed ht (Finset.erase_subset _ _) hne),
        h.image_erase_left ht hvt]
    _ = ⋃ v ∈ s.image φ, convexHull ℝ (((t.image φ).erase v : Finset F) : Set F) := by
      ext x
      simp only [mem_iUnion, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, hx⟩
        exact ⟨φ v, ⟨v, hv, rfl⟩, hx⟩
      · rintro ⟨v, ⟨w, hw, rfl⟩, hx⟩
        exact ⟨w, hw, hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
