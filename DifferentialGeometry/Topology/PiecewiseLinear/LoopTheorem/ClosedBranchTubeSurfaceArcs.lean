/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCrossingArcs
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSurfaceSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_subdivision_branchSurface_arcs
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ R₀ : Geometry.SimplicialComplex ℝ E, Finite R₀.faces → IsSubdivision R₀ L →
        ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R R₀ ∧ R.faces.Finite ∧
          (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space =
            Subtype.val '' hD.singularSet.branchCarrier c ∧
          let Γ := PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)
          ∀ s ∈ Γ.faces, ∀ y₀ y₁ : E,
            Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁} →
            ∃ (P : Fin 4 → Set E) (γ : Fin 4 → ℝ → E),
              (∀ i, IsPLBall 2 (P i) ∧ (PiecewiseLinear.restrict R (P i)).space = P i ∧
                IsPLHomeomorphOn (γ i) (Icc 0 1)
                  ((derivedNeighborhoodCellBase R s).space ∩ P i) ∧
                γ i 0 = y₀ ∧ γ i 1 = y₁ ∧
                ∀ t ∈ Γ.faces, (s ⊆ t ∨ t ⊆ s) →
                  t ∈ (boundaryComplex 2 (PiecewiseLinear.restrict R (P i))).faces) ∧
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
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc R₀ hR₀fin hR₀L
  obtain ⟨t, R, ψ, V, Ω, W, P, q, hRR₀, hRfin, hΓR, hcharts, hcells⟩ :=
    exists_subdivision_branchSurface_disks L hL hD hc R₀ hR₀fin hR₀L
  let _ : Finite R.faces := hRfin.to_subtype
  have hRL : R.space = L.space := (hRR₀.trans hR₀L).space_eq
  let Γ := PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)
  have hΓsp : Γ.space = Subtype.val '' hD.singularSet.branchCarrier c := hΓR
  have hΓfaces : Γ.faces ⊆ R.faces := restrict_faces_subset R _
  refine ⟨R, hRR₀, hRfin, hΓR, ?_⟩
  dsimp only
  intro s hs y₀ y₁ hpoles
  obtain ⟨j, hstar, hcell⟩ := hcells s hs
  obtain ⟨-, -, -, hWΩ, hψ, -, hΓchart, hdata⟩ := hcharts j
  have hψR : IsPLHomeomorphOn (ψ j) (V j) (R.space ∩ Ω j) := hRL.symm ▸ hψ
  have hΓχ : ∀ p ∈ V j, ψ j p ∈ Γ.space ↔ p.1 = 0 := by
    rw [hΓsp]
    exact hΓchart
  have hread : ∀ x ∈ R.space ∩ W j, ∀ i,
      x ∈ P j i ↔ Function.invFunOn (ψ j) (V j) x ∈ crossHalfPlane i := by
    intro x hx i
    rw [hRL] at hx
    exact ((hdata i).2.2.2 x hx).1
  have hbd : ∀ x ∈ R.space ∩ W j, ∀ i,
      x ∈ q j i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space := by
    intro x hx i
    rw [hRL] at hx
    rw [hΓsp]
    exact ((hdata i).2.2.2 x hx).2
  obtain ⟨γ, hγ, hγ0, hγ1, hTT, hsep⟩ := exists_fourArcTrace_of_crossHalfPlane_disks R Γ
    hΓfaces hs hψR hWΩ hΓχ (fun i => (hdata i).1) (fun i => (hdata i).2.2.1)
    hread hbd hcell hpoles
  refine ⟨P j, γ, fun i => ?_, hTT, hsep⟩
  refine ⟨⟨q j i, (hdata i).1⟩, (hdata i).2.2.1, hγ i, hγ0 i, hγ1 i,
    fun u hu hcomp => ?_⟩
  let A := PiecewiseLinear.restrict R (P j i)
  let _ : Finite A.faces := (restrict_faces_finite R _).to_subtype
  have hAsp : A.space = P j i := (hdata i).2.2.1
  have hAbd := (hdata i).1.image_stdSimplexBoundary_eq_boundaryComplex A hAsp
  have hcommon : ∃ v, v ∈ s ∧ v ∈ u := by
    rcases hcomp with h | h
    · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hs
      exact ⟨v, hv, h hv⟩
    · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hu
      exact ⟨v, h hv, hv⟩
  obtain ⟨v, hvs, hvu⟩ := hcommon
  have hcentroidHull : u.centroid ℝ id ∈ convexHull ℝ (u : Set E) :=
    u.centroid_mem_convexHull (Γ.nonempty_of_mem_faces hu)
  have hcentroidW : u.centroid ℝ id ∈ W j :=
    hstar (mem_iUnion₂.mpr ⟨v, hvs, mem_iUnion₂.mpr
      ⟨u, ⟨hΓfaces hu, subset_convexHull ℝ _ hvu⟩, hcentroidHull⟩⟩)
  apply mem_faces_of_mem_openSimplex_of_mem_space
    ((boundaryComplex_faces_subset 2 A).trans (restrict_faces_subset R _)) (hΓfaces hu)
    (centroid_mem_openSimplex_of_mem_faces R u (hΓfaces hu))
  rw [← hAbd]
  exact (hbd _ ⟨R.convexHull_subset_space (hΓfaces hu) hcentroidHull, hcentroidW⟩ i).mpr
    (Γ.convexHull_subset_space hu hcentroidHull)

end DifferentialGeometry.Topology.PiecewiseLinear
