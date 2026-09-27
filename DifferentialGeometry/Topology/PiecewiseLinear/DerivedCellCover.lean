/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells
import DifferentialGeometry.Topology.PiecewiseLinear.StarSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isSubdivision_derivedCells_subset_cover
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {Γ : Set E} (hΓ : IsPolyhedron Γ) (hΓK : Γ ⊆ K.space)
    {ι : Type*} [Finite ι] (P : ι → Set E) (hP : ∀ i, IsPolyhedron (P i))
    (hPK : ∀ i, P i ⊆ K.space) {κ : Type*} (U : κ → Set E) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x ∈ Γ, ∃ i, x ∈ U i) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      (PiecewiseLinear.restrict R Γ).space = Γ ∧
      (∀ i, (PiecewiseLinear.restrict R (P i)).space = P i) ∧
      ∀ s ∈ (PiecewiseLinear.restrict R Γ).faces,
        ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ U i ∧
          (derivedNeighborhoodCell R s).space ⊆ U i := by
  let Q : Option ι → Set E := Option.elim' Γ P
  have hQ : ∀ j, IsPolyhedron (Q j) := by
    intro j
    cases j with
    | none => exact hΓ
    | some i => exact hP i
  have hQK : ∀ j, Q j ⊆ K.space := by
    intro j
    cases j with
    | none => exact hΓK
    | some i => exact hPK i
  let V : Option κ → Set E := Option.elim' Γᶜ U
  have hV : ∀ j, IsOpen (((↑) : K.space → E) ⁻¹' V j) := by
    intro j
    cases j with
    | none => exact hΓ.isClosed.isOpen_compl.preimage continuous_subtype_val
    | some i => exact (hU i).preimage continuous_subtype_val
  have hVK : K.space ⊆ ⋃ j, V j := by
    intro x _
    by_cases hx : x ∈ Γ
    · obtain ⟨i, hi⟩ := hcover x hx
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩
  obtain ⟨R, hRK, hRfin, hQR, hstars⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K Q hQ hQK V hV hVK
  let _ : Finite R.faces := hRfin.to_subtype
  have hΓR : (PiecewiseLinear.restrict R Γ).space = Γ := hQR none
  refine ⟨R, hRK, hRfin, hΓR, fun i => hQR (some i), fun s hs => ?_⟩
  have hsR := (mem_restrict_faces_iff R Γ).mp hs
  have hc : {s.centroid ℝ id} ∈ (secondDerived R).faces :=
    (barycentricSubdivision_isSubdivision (barycentricSubdivision R)).singleton_mem
      (singleton_centroid_mem_barycentricSubdivision R hsR.1)
  have hcell : (derivedNeighborhoodCell R s).space ⊆ ⋃ v ∈ s, closedStar R v := by
    rw [derivedNeighborhoodCell_space_eq_closedStar R hsR.1]
    exact (closedStar_subset_of_isSubdivision (secondDerived_isSubdivision R) _).trans
      (closedStar_subset_biUnion_of_mem_convexHull R hsR.1
        (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hsR.1)))
  obtain ⟨j, hj⟩ := hstars s hsR.1
  cases j with
  | none =>
    have hcentroid : s.centroid ℝ id ∈ Γ :=
      hsR.2 (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hsR.1))
    have hcentroidCell : s.centroid ℝ id ∈ (derivedNeighborhoodCell R s).space := by
      rw [derivedNeighborhoodCell_space_eq_closedStar R hsR.1]
      exact mem_closedStar_self _ hc
    exact (hj (hcell hcentroidCell) hcentroid).elim
  | some i => exact ⟨i, hj, hcell.trans hj⟩

end DifferentialGeometry.Topology.PiecewiseLinear
