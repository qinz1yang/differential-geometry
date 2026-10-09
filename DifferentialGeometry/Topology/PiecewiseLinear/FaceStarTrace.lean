/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryTraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [dE : DecidableEq E] [dP : DecidableEq (EuclideanSpace ℝ (Fin 2))]

open Classical in
theorem boundaryComplex_faceStarComplex_inter_convexHull_of_isGlueIso_planar
    {K : Geometry.SimplicialComplex ℝ E}
    {L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    [Finite K.faces] [Finite L.faces]
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (h : IsGlueIso K L φ ψ) (hL : IsPLBall 2 L.space)
    {t s : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3)
    (hs : s ∈ K.faces) (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : (boundaryComplex 2 K).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)) :
    (boundaryComplex 2 (faceStarComplex K s)).space ∩ convexHull ℝ (t : Set E) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E) ∧
      (faceStarComplex K s).space ≠ convexHull ℝ (t : Set E) := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdP : dP = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  let P := faceStarComplex K s
  let Q := faceStarComplex L (s.image φ)
  let _ : Finite P.faces := (faceStarComplex_faces_finite K s).to_subtype
  let _ : Finite Q.faces := (faceStarComplex_faces_finite L (s.image φ)).to_subtype
  have hK := hL.of_isPLHomeomorphOn h.symm.isPLHomeomorphOn
  have hQ : IsPLBall 2 Q.space :=
    hL.isCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex L (h.image₁ _ hs)
  have htL := h.image₁ _ ht
  have hsL := h.image₁ _ hs
  have hstL := Finset.image_mono φ hst
  have htLcard : (t.image φ).card = 3 := (h.card_image_left ht).trans htcard
  have hsLcard : (s.image φ).card = 1 ∨ (s.image φ).card = 2 := by
    rwa [h.card_image_left hs]
  have htQ : t.image φ ∈ Q.faces := mem_faceStarComplex_faces_of_subset L htL hstL
  have htraceL := h.boundaryComplex_inter_convexHull_image
    hK.isCombinatorialManifoldWithBoundary ht hst (by omega) htrace
  rw [← frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary] at htraceL
  have htraceQ : frontier Q.space ∩ convexHull ℝ ((t.image φ : Finset _) : Set _) =
      ⋃ v ∈ s.image φ, convexHull ℝ (((t.image φ).erase v : Finset _) : Set _) := by
    simpa only [Q, Finset.coe_erase] using
      frontier_faceStarComplex_inter_convexHull L htL hstL
        (by simpa only [Finset.coe_erase] using htraceL)
  have hPQ : IsGlueIso P Q φ ψ := h.faceStarComplex hs
  have hneQ : Q.space ≠ convexHull ℝ ((t.image φ : Finset _) : Set _) := by
    intro heq
    let x := (s.image φ).centroid ℝ id
    have hx : x ∈ openSimplex (s.image φ) := centroid_mem_openSimplex (L.nonempty_of_mem_faces hsL)
    have hxint := openSimplex_subset_interior_of_frontier_inter_eq Q htQ hstL
      (by simpa only [Finset.coe_erase] using htraceQ) hx
    have hxfront : x ∈ frontier (convexHull ℝ ((t.image φ : Finset _) : Set _)) := by
      rw [frontier_convexHull_eq_simplexBoundary (L.indep htL) (by simpa using htLcard)]
      apply (simplexBoundary (t.image φ) (L.indep htL)).convexHull_subset_space
        ⟨hstL, L.nonempty_of_mem_faces hsL, ?_⟩ (openSimplex_subset_convexHull (s.image φ) hx)
      intro heq'
      have hc := congrArg Finset.card heq'
      rcases hsLcard with hc' | hc' <;> omega
    exact hxfront.2 (heq ▸ hxint)
  constructor
  · have htraceQ' : (boundaryComplex 2 Q).space ∩ convexHull ℝ ((t.image φ : Finset _) : Set _) =
        ⋃ v ∈ s.image φ, convexHull ℝ (((t.image φ).erase v : Finset _) : Set _) := by
      rw [← frontier_space_eq_boundaryComplex_space hQ.isCombinatorialManifoldWithBoundary]
      exact htraceQ
    have hback := hPQ.symm.boundaryComplex_inter_convexHull_image
      hQ.isCombinatorialManifoldWithBoundary htQ hstL (by omega) htraceQ'
    simpa only [h.image_image_left ht, h.image_image_left hs] using hback
  · intro heq
    apply hneQ
    rw [← hPQ.image_left, heq]
    exact hPQ.image_convexHull (mem_faceStarComplex_faces_of_subset K ht hst)

end DifferentialGeometry.Topology.PiecewiseLinear
