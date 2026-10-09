/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeSphereBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairModel
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_singleton_cap_boundary_inter_surface
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hLK : L.faces ⊆ K.faces) {s t : Finset E}
    (hs : s ∈ (boundaryComplex 2 L).faces) (ht : t ∈ (boundaryComplex 2 L).faces)
    (hne : s ≠ t) (hcomp : s ⊆ t ∨ t ⊆ s) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space)) :
    ∃ x : E, q '' stdSimplexBoundary 2 ∩
      ((derivedNeighborhoodCellBase K s).space ∩ L.space) = {x} ∧
      ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) ∩ L.space =
        segment ℝ (({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id) x := by
  have hsL := boundaryComplex_faces_subset 2 L hs
  have htL := boundaryComplex_faces_subset 2 L ht
  have hsK := hLK hsL
  have htK := hLK htL
  let e : Finset E := {s.centroid ℝ id, t.centroid ℝ id}
  have he : e ∈ (barycentricSubdivision K).faces :=
    pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hsK htK hcomp
  let A := dualCell (barycentricSubdivision K) e he
  let _ : Finite A.faces := (dualCell_faces_finite _ he).to_subtype
  let _ : Finite (upperLink (barycentricSubdivision K) e).faces :=
    (upperLink_faces_finite _ _).to_subtype
  have hAspace : A.space =
      (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space :=
    (derivedNeighborhoodCell_space_inter K hsK htK hcomp).symm
  have hqb := hq.image_stdSimplexBoundary_eq_boundaryComplex A hAspace
  have hS : IsPLSphere 1 (upperLink (barycentricSubdivision K) e).space :=
    hK.isPLSphere_upperLink_pair_centroid hsK htK hne hcomp
  have hAb : (boundaryComplex 2 A).space =
      (upperLink (barycentricSubdivision K) e).space :=
    (isConeBase_upperLink (barycentricSubdivision K) he).boundaryComplex_space_of_isPLSphere hS
  let _ : Finite (boundaryComplex 2 L).faces := (boundaryComplex_faces_finite 2 L).to_subtype
  have heB : e ∈ (boundaryComplex 2 (barycentricSubdivision L)).faces := by
    rw [boundaryComplex_barycentricSubdivision L hL]
    exact pair_centroid_mem_barycentricSubdivision_of_subset_or_subset _ hs ht hcomp
  have hecard : e.card = 1 + 1 :=
    Finset.card_pair (centroid_ne_centroid_of_ne K hsK htK hne)
  have hball : IsPLBall 0 (upperLink (barycentricSubdivision L) e).space :=
    hL.barycentricSubdivision.isPLBall_upperLink_of_mem_boundaryComplex _ heB hecard
  obtain ⟨x, hx⟩ := isPLBall_zero_iff.mp hball
  have hsub : (upperLink (barycentricSubdivision K) e).space ⊆
      (derivedNeighborhoodCellBase K s).space := by
    apply space_mono_of_faces_subset
    rintro u ⟨d, hd, hdne, hlt, rfl⟩
    refine ⟨d, hd, hdne, fun f hf => ?_, rfl⟩
    exact (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)).trans_ssubset
      (hlt f hf)
  refine ⟨x, ?_, ?_⟩
  · rw [hqb, hAb]
    calc
      (upperLink (barycentricSubdivision K) e).space ∩
          ((derivedNeighborhoodCellBase K s).space ∩ L.space) =
          (upperLink (barycentricSubdivision K) e).space ∩ L.space := by
        ext y
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hsub h.1, h.2⟩⟩
      _ = (upperLink (barycentricSubdivision L) e).space := by
        rw [← (barycentricSubdivision_isSubdivision L).space_eq]
        exact upperLink_space_inter_subcomplex _ _ (barycentricSubdivision_faces_subset hLK) e
      _ = {x} := hx
  · calc
      ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) ∩ L.space =
          ((derivedNeighborhoodCell K s).space ∩ L.space) ∩
            ((derivedNeighborhoodCell K t).space ∩ L.space) := by
        ext y
        simp only [mem_inter_iff]
        tauto
      _ = (derivedNeighborhoodCell L s).space ∩ (derivedNeighborhoodCell L t).space := by
        rw [derivedNeighborhoodCell_inter_subcomplex K L hLK hsL,
          derivedNeighborhoodCell_inter_subcomplex K L hLK htL]
      _ = coneSet (e.centroid ℝ id) (upperLink (barycentricSubdivision L) e).space :=
        derivedNeighborhoodCell_inter_eq_coneSet L hsL htL hcomp
      _ = segment ℝ (e.centroid ℝ id) x := by
        rw [hx, coneSet_eq_iUnion_segment (singleton_nonempty x), biUnion_singleton]

end DifferentialGeometry.Topology.PiecewiseLinear
