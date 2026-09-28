/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedSurfaceCap
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeDerivedCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem pair_centroid_not_mem_derived_cap_boundary
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces] (hR : IsCombinatorialManifold 3 R)
    {s t : Finset E} (hs : s ∈ R.faces) (ht : t ∈ R.faces)
    (hne : s ≠ t) (hcomp : s ⊆ t ∨ t ⊆ s) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      ((derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space)) :
    ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id ∉
      q '' stdSimplexBoundary 2 := by
  let e : Finset E := {s.centroid ℝ id, t.centroid ℝ id}
  have he : e ∈ (barycentricSubdivision R).faces :=
    pair_centroid_mem_barycentricSubdivision_of_subset_or_subset R hs ht hcomp
  let B := dualCell (barycentricSubdivision R) e he
  let _ : Finite B.faces := (dualCell_faces_finite _ he).to_subtype
  let _ : Finite (upperLink (barycentricSubdivision R) e).faces :=
    (upperLink_faces_finite _ _).to_subtype
  have hB : B.space = (derivedNeighborhoodCell R s).space ∩
      (derivedNeighborhoodCell R t).space :=
    (derivedNeighborhoodCell_space_inter R hs ht hcomp).symm
  have hcone := isConeBase_upperLink (barycentricSubdivision R) he
  have hbd : (boundaryComplex 2 B).space = (upperLink (barycentricSubdivision R) e).space :=
    hcone.boundaryComplex_space_of_isPLSphere
      (hR.isPLSphere_upperLink_pair_centroid hs ht hne hcomp)
  rw [hq.image_stdSimplexBoundary_eq_boundaryComplex B hB, hbd]
  exact hcone.notMem_space

open Classical in
theorem exists_derived_cap_surface_segment
    (R A : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite A.faces]
    (hR : IsCombinatorialManifold 3 R) (hA : IsCombinatorialManifoldWithBoundary 2 A)
    (hAR : A.faces ⊆ R.faces) {s t : Finset E}
    (hs : s ∈ (boundaryComplex 2 A).faces) (ht : t ∈ (boundaryComplex 2 A).faces)
    (hne : s ≠ t) (hcomp : s ⊆ t ∨ t ⊆ s) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      ((derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space)) :
    ∃ x : E,
      q '' stdSimplexBoundary 2 ∩ ((derivedNeighborhoodCellBase R s).space ∩ A.space) = {x} ∧
      ((derivedNeighborhoodCellBase R s).space ∩ A.space) ∩
        ((derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space) =
        segment ℝ (({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id) x ∧
      ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id ≠ x := by
  have hsR := hAR (boundaryComplex_faces_subset 2 A hs)
  have htR := hAR (boundaryComplex_faces_subset 2 A ht)
  obtain ⟨x, hbd, hseg⟩ :=
    exists_singleton_cap_boundary_inter_surface R A hR hA hAR hs ht hne hcomp hq
  refine ⟨x, hbd, ?_, ?_⟩
  · have hsub := derivedNeighborhoodCell_inter_subset_base R hsR htR hne
    convert hseg using 1
    ext y
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  · intro hcx
    have hx : x ∈ q '' stdSimplexBoundary 2 := (hbd.symm ▸ mem_singleton x).1
    exact pair_centroid_not_mem_derived_cap_boundary R hR hsR htR hne hcomp hq (hcx.symm ▸ hx)

omit [FiniteDimensional ℝ E] in
open Classical in
theorem derived_cap_core_eq_pole
    (R Γ : Geometry.SimplicialComplex ℝ E) (hΓR : Γ.faces ⊆ R.faces)
    {s t : Finset E} (hs : s ∈ Γ.faces) (ht : t ∈ Γ.faces)
    (hcomp : s ⊆ t ∨ t ⊆ s) {D₀ D₁ : Set E} {y₀ y₁ : E}
    (hcap : (derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space = D₁)
    (hD₁S : D₁ ⊆ (derivedNeighborhoodCellBase R s).space)
    (hpoles : Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁})
    (hdis : Disjoint D₀ D₁) (hy₀ : y₀ ∈ D₀) (hy₁ : y₁ ∈ D₁) :
    Γ.space ∩ D₁ = {y₁} ∧
      ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id = y₁ := by
  have hcore : Γ.space ∩ D₁ = {y₁} := by
    ext y
    constructor
    · rintro ⟨hyΓ, hyD⟩
      have hy : y ∈ ({y₀, y₁} : Set E) := hpoles.subset ⟨hyΓ, hD₁S hyD⟩
      rcases hy with rfl | h
      · exact (disjoint_left.mp hdis hy₀ hyD).elim
      · exact h
    · rintro rfl
      exact ⟨(hpoles.symm.subset (Or.inr rfl)).1, hy₁⟩
  refine ⟨hcore, ?_⟩
  apply hcore.subset
  refine ⟨pair_centroid_mem_space_of_subset hs ht hcomp, ?_⟩
  rw [← hcap, derivedNeighborhoodCell_inter_eq_coneSet R (hΓR hs) (hΓR ht) hcomp]
  exact mem_coneSet_iff.mpr (Or.inl rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
