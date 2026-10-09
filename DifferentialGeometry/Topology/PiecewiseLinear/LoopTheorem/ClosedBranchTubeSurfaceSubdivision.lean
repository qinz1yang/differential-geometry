/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCover
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSourceSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSurfaceCharts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_subdivision_branchSurface_disks
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ R₀ : Geometry.SimplicialComplex ℝ E, Finite R₀.faces → IsSubdivision R₀ L →
        ∃ (t : Finset (hD.singularSet.branchCarrier c)) (R : Geometry.SimplicialComplex ℝ E)
          (ψ : t → (ℝ × ℝ) × ℝ → E) (V : t → Set ((ℝ × ℝ) × ℝ))
          (Ω W : t → Set E) (P : t → Fin 4 → Set E) (q : t → Fin 4 → (Fin 3 → ℝ) → E),
          IsSubdivision R R₀ ∧ R.faces.Finite ∧
          (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space =
            Subtype.val '' hD.singularSet.branchCarrier c ∧
          (∀ j, IsOpen (V j) ∧ IsOpen (Ω j) ∧ IsOpen (W j) ∧ W j ⊆ Ω j ∧
            IsPLHomeomorphOn (ψ j) (V j) (L.space ∩ Ω j) ∧
            (∀ p ∈ V j, ψ j p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes) ∧
            (∀ p ∈ V j,
              ψ j p ∈ Subtype.val '' hD.singularSet.branchCarrier c ↔ p.1 = 0) ∧
            ∀ i, IsPLHomeomorphOn (q j i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P j i) ∧
              P j i ⊆ L.space ∩ Subtype.val '' (D '' D.domain) ∧
              (PiecewiseLinear.restrict R (P j i)).space = P j i ∧
              ∀ x ∈ L.space ∩ W j,
                (x ∈ P j i ↔ Function.invFunOn (ψ j) (V j) x ∈ crossHalfPlane i) ∧
                (x ∈ q j i '' stdSimplexBoundary 2 ↔
                  x ∈ Subtype.val '' hD.singularSet.branchCarrier c)) ∧
          ∀ s ∈ (PiecewiseLinear.restrict R
              (Subtype.val '' hD.singularSet.branchCarrier c)).faces,
            ∃ j, (⋃ v ∈ s, closedStar R v) ⊆ W j ∧
              (derivedNeighborhoodCell R s).space ⊆ W j := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc R₀ hR₀fin hR₀L
  let _ : Finite R₀.faces := hR₀fin
  let Y := hD.singularSet.branchCarrier c
  choose ψ V Ω W P q hV hΩ hW hyW hWΩ hψ hF hΓ hq hP hread hbd using
    (fun y : Y => exists_branchSurface_disks L hL hD hc y.1 y.2)
  have hcover : Y ⊆ ⋃ y : Y, Subtype.val ⁻¹' W y := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hyW ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := (hD.singularSet.branchCarrier_isCompact c).elim_finite_subcover
    (fun y : Y => Subtype.val ⁻¹' W y) (fun y => (hW y).preimage continuous_subtype_val) hcover
  have hcoverE : ∀ x ∈ Subtype.val '' Y, ∃ j : t, x ∈ W j.1 := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨j, hjt, hyj⟩ := mem_iUnion₂.mp (ht hy)
    exact ⟨⟨j, hjt⟩, hyj⟩
  have hΓpoly : IsPolyhedron (Subtype.val '' Y) :=
    (isPLSphere_one_val_image_branchCarrier L hL D BdM hD.singularSet c hc).isPolyhedron
  have hΓR₀ : Subtype.val '' Y ⊆ R₀.space := by
    rintro x ⟨y, -, rfl⟩
    exact hR₀L.space_eq.symm ▸ y.2
  have hPpoly : ∀ j : t × Fin 4, IsPolyhedron (P j.1.1 j.2) := fun j =>
    (show IsPLBall 2 (P j.1.1 j.2) from ⟨q j.1.1 j.2, hq j.1.1 j.2⟩).isPolyhedron
  have hPR₀ : ∀ j : t × Fin 4, P j.1.1 j.2 ⊆ R₀.space := by
    intro j x hx
    exact hR₀L.space_eq.symm ▸ (hP j.1.1 j.2 hx).1
  obtain ⟨R, hRR₀, hRfin, hΓR, hPR, hcells⟩ :=
    exists_isSubdivision_derivedCells_subset_cover R₀ hΓpoly hΓR₀
      (fun j : t × Fin 4 => P j.1.1 j.2) hPpoly hPR₀
      (fun j : t => W j.1) (fun j => hW j.1) hcoverE
  refine ⟨t, R, fun j => ψ j.1, fun j => V j.1, fun j => Ω j.1, fun j => W j.1,
    fun j => P j.1, fun j => q j.1, hRR₀, hRfin, hΓR, ?_, hcells⟩
  intro j
  refine ⟨hV j.1, hΩ j.1, hW j.1, hWΩ j.1, hψ j.1, hF j.1, hΓ j.1, fun i => ?_⟩
  exact ⟨hq j.1 i, hP j.1 i, hPR (j, i), fun x hx =>
    ⟨hread j.1 x hx i, hbd j.1 x hx i⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
