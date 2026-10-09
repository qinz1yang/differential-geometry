/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedSurfaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneSeparation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_fourArcTrace_of_crossHalfPlane_disks
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hΓR : Γ.faces ⊆ R.faces) {s : Finset E} (hs : s ∈ Γ.faces)
    {ψ : (ℝ × ℝ) × ℝ → E} {V : Set ((ℝ × ℝ) × ℝ)} {Ω W : Set E}
    (hψ : IsPLHomeomorphOn ψ V (R.space ∩ Ω)) (hWΩ : W ⊆ Ω)
    (hΓ : ∀ p ∈ V, ψ p ∈ Γ.space ↔ p.1 = 0)
    {P : Fin 4 → Set E} {q : Fin 4 → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i))
    (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    (hread : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i)
    (hbd : ∀ x ∈ R.space ∩ W, ∀ i, x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hcell : (derivedNeighborhoodCell R s).space ⊆ W) {y₀ y₁ : E}
    (hpoles : Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁}) :
    ∃ γ : Fin 4 → ℝ → E,
      (∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1)
        ((derivedNeighborhoodCellBase R s).space ∩ P i)) ∧
      (∀ i, γ i 0 = y₀) ∧ (∀ i, γ i 1 = y₁) ∧
      (∀ i j, i ≠ j →
        ((derivedNeighborhoodCellBase R s).space ∩ P i) ∩
          ((derivedNeighborhoodCellBase R s).space ∩ P j) = {y₀, y₁}) ∧
      ∀ i : Fin 4,
        ∀ U ⊆ (derivedNeighborhoodCellBase R s).space \
          (((derivedNeighborhoodCellBase R s).space ∩ P i) ∪
            ((derivedNeighborhoodCellBase R s).space ∩ P (i + 2))),
          IsPreconnected U →
          (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 1))).Nonempty →
          (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 3))).Nonempty → False := by
  let S := (derivedNeighborhoodCellBase R s).space
  let χ := Function.invFunOn ψ V
  have hSR : S ⊆ (derivedNeighborhoodCell R s).space := by
    rw [derivedNeighborhoodCell_space_eq_coneSet R (hΓR hs)]
    exact subset_coneSet _ _
  have hSW : S ⊆ R.space ∩ W := fun x hx =>
    ⟨derivedNeighborhoodCell_space_subset R s (hSR hx), hcell (hSR hx)⟩
  have hSΩ : S ⊆ R.space ∩ Ω := fun x hx => ⟨(hSW hx).1, hWΩ (hSW hx).2⟩
  have hχV : ∀ x ∈ S, χ x ∈ V := fun x hx =>
    hψ.bijOn.surjOn.mapsTo_invFunOn (hSΩ hx)
  have hψχ : ∀ x ∈ S, ψ (χ x) = x := fun x hx => hψ.bijOn.invOn_invFunOn.2 (hSΩ hx)
  have hχΓ : ∀ x ∈ S, (χ x).1 = 0 ↔ x ∈ Γ.space := by
    intro x hx
    rw [← hΓ _ (hχV x hx), hψχ x hx]
  have hχread : ∀ x ∈ S, ∀ i, x ∈ P i ↔ χ x ∈ crossHalfPlane i :=
    fun x hx i => hread x (hSW hx) i
  have hparam : ∀ i : Fin 4, ∃ γ : ℝ → E,
      IsPLHomeomorphOn γ (Icc 0 1) (S ∩ P i) ∧ γ 0 = y₀ ∧ γ 1 = y₁ := by
    intro i
    let A := PiecewiseLinear.restrict R (P i)
    let _ : Finite A.faces := (restrict_faces_finite R (P i)).to_subtype
    have hAsp : A.space = P i := hPR i
    have hAball : IsPLBall 2 A.space := hAsp.symm ▸ (show IsPLBall 2 (P i) from ⟨q i, hq i⟩)
    have hAbd := (hq i).image_stdSimplexBoundary_eq_boundaryComplex A hAsp
    have hcentroidCell : s.centroid ℝ id ∈ (derivedNeighborhoodCell R s).space := by
      rw [derivedNeighborhoodCell_space_eq_coneSet R (hΓR hs)]
      exact apex_mem_coneSet _ _
    have hcentroidΓ : s.centroid ℝ id ∈ Γ.space :=
      Γ.convexHull_subset_space hs (s.centroid_mem_convexHull (Γ.nonempty_of_mem_faces hs))
    have hsA : s ∈ (boundaryComplex 2 A).faces := by
      apply mem_faces_of_mem_openSimplex_of_mem_space
        ((boundaryComplex_faces_subset 2 A).trans (restrict_faces_subset R (P i))) (hΓR hs)
        (centroid_mem_openSimplex_of_mem_faces R s (hΓR hs))
      rw [← hAbd]
      exact (hbd _ ⟨derivedNeighborhoodCell_space_subset R s hcentroidCell,
        hcell hcentroidCell⟩ i).mpr hcentroidΓ
    have hboundary : S ∩ (boundaryComplex 2 A).space = {y₀, y₁} := by
      calc
        S ∩ (boundaryComplex 2 A).space = S ∩ Γ.space := by
          ext x
          constructor
          · rintro ⟨hxS, hxB⟩
            rw [← hAbd] at hxB
            exact ⟨hxS, (hbd x (hSW hxS) i).mp hxB⟩
          · rintro ⟨hxS, hxΓ⟩
            refine ⟨hxS, ?_⟩
            rw [← hAbd]
            exact (hbd x (hSW hxS) i).mpr hxΓ
        _ = {y₀, y₁} := (inter_comm _ _).trans hpoles
    obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_parametrization_derivedNeighborhoodCellBase_inter
      R A hAball.isCombinatorialManifoldWithBoundary (restrict_faces_subset R (P i)) hsA hboundary
    exact ⟨γ, hAsp ▸ hγ, hγ0, hγ1⟩
  choose γ hγ hγ0 hγ1 using hparam
  refine ⟨γ, hγ, hγ0, hγ1, ?_, ?_⟩
  · intro i j hij
    ext x
    constructor
    · rintro ⟨⟨hxS, hxi⟩, ⟨-, hxj⟩⟩
      have haxis : (χ x).1 = 0 := by
        have hmem : χ x ∈ crossHalfPlane i ∩ crossHalfPlane j :=
          ⟨(hχread x hxS i).mp hxi, (hχread x hxS j).mp hxj⟩
        exact (crossHalfPlane_inter hij).subset hmem
      exact hpoles.subset ⟨(hχΓ x hxS).mp haxis, hxS⟩
    · intro hx
      obtain ⟨hxΓ, hxS⟩ := hpoles.symm.subset hx
      have hPi : ∀ k, x ∈ S ∩ P k := fun k =>
        ⟨hxS, (hχread x hxS k).mpr ⟨0, le_rfl, by rw [zero_smul]; exact (hχΓ x hxS).mpr hxΓ⟩⟩
      exact ⟨hPi i, hPi j⟩
  · intro i U hU hconn hpos hneg
    have hUS : U ⊆ S := hU.trans sdiff_subset
    have hcont : ContinuousOn χ U :=
      hψ.isPiecewiseAffineOn_invFunOn.continuousOn.mono (hUS.trans hSΩ)
    apply crossHalfPlane_separated i (U := χ '' U) ?_ (hconn.image χ hcont) ?_ ?_
    · rintro p ⟨x, hx, rfl⟩ hhalf
      apply (hU hx).2
      rcases hhalf with hi | hi
      · exact Or.inl ⟨hUS hx, (hχread x (hUS hx) i).mpr hi⟩
      · exact Or.inr ⟨hUS hx, (hχread x (hUS hx) (i + 2)).mpr hi⟩
    · obtain ⟨x, hxU, hxS, hxP⟩ := hpos
      exact ⟨χ x, mem_image_of_mem χ hxU, (hχread x hxS (i + 1)).mp hxP⟩
    · obtain ⟨x, hxU, hxS, hxP⟩ := hneg
      exact ⟨χ x, mem_image_of_mem χ hxU, (hχread x hxS (i + 3)).mp hxP⟩

end DifferentialGeometry.Topology.PiecewiseLinear
