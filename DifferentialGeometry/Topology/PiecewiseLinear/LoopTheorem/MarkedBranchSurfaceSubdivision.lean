/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCover
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MarkedBranchSurfaceCharts
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSourceSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_subdivision_marked_branchSurface_disks
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
        {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
        {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)},
        hD.IsBranchDeckInvolution c J τ → hD.IsTwoSidedBranchCollar c J Q C ρ →
        ∀ R₀ : Geometry.SimplicialComplex ℝ E, Finite R₀.faces → IsSubdivision R₀ L →
          ∃ (t : Finset J) (R : Geometry.SimplicialComplex ℝ E)
            (ψ : t → (ℝ × ℝ) × ℝ → E) (V : t → Set ((ℝ × ℝ) × ℝ))
            (Ω W : t → Set E) (A : t → Bool → Set (EuclideanSpace ℝ (Fin 2)))
            (P : t → Fin 4 → Set E) (q : t → Fin 4 → (Fin 3 → ℝ) → E),
            IsSubdivision R R₀ ∧ R.faces.Finite ∧
            (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space =
              Subtype.val '' hD.singularSet.branchCarrier c ∧
            (∀ j, IsOpen (V j) ∧ IsOpen (Ω j) ∧ IsOpen (W j) ∧ W j ⊆ Ω j ∧
              IsPLHomeomorphOn (ψ j) (V j) (L.space ∩ Ω j) ∧
              (∀ p ∈ V j, ψ j p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes) ∧
              (∀ p ∈ V j,
                ψ j p ∈ Subtype.val '' hD.singularSet.branchCarrier c ↔ p.1 = 0) ∧
              (∀ b, IsCompact (A j b) ∧ A j b ⊆ C ∧ InjOn D (A j b)) ∧
              Disjoint (A j false) (A j true) ∧
              (∀ x ∈ D.domain, ((D x : L.space) : E) ∈ W j →
                x ∈ A j false ∪ A j true) ∧
              (∀ b, ∀ y ∈ hD.singularSet.branchCarrier c,
                (y : E) ∈ W j → y ∈ D '' (A j b ∩ J)) ∧
              ∀ i, IsPLHomeomorphOn (q j i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P j i) ∧
                P j i ⊆ L.space ∩ Subtype.val '' (D '' D.domain) ∧
                (PiecewiseLinear.restrict R (P j i)).space = P j i ∧
                ∀ x ∈ L.space ∩ W j,
                  (x ∈ P j i ↔ Function.invFunOn (ψ j) (V j) x ∈ crossHalfPlane i) ∧
                  (x ∈ P j i ↔ x ∈ (Subtype.val ∘ D) ''
                    (A j (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2)) ∧
                  (x ∈ q j i '' stdSimplexBoundary 2 ↔
                    x ∈ Subtype.val '' hD.singularSet.branchCarrier c)) ∧
            ∀ s ∈ (PiecewiseLinear.restrict R
                (Subtype.val '' hD.singularSet.branchCarrier c)).faces,
              ∃ j, (⋃ v ∈ s, closedStar R v) ⊆ W j ∧
                (derivedNeighborhoodCell R s).space ⊆ W j := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J Q C τ ρ hτ hρ R₀ hR₀fin hR₀L
  let _ : Finite R₀.faces := hR₀fin
  choose ψ V Ω W A P q hV hΩ hW haW hWΩ hψ hF hΓ hA hAA haA hτaA hpre hcore hq
    hread hsource hbd using
      (fun a : J => exists_marked_branchSurface_disks L hL hD hc hτ hρ a.1 a.2)
  let Y := hD.singularSet.branchCarrier c
  have hcover : Y ⊆ ⋃ a : J, Subtype.val ⁻¹' W a := by
    intro y hy
    obtain ⟨a, haD, b, hbD, hab, hay, hby⟩ :=
      hD.singularSet.branchCarrier_subset_doublePointSet c hy
    have haJ : a ∈ J := hτ.1 ▸ (show a ∈ hD.branchPreimage c from ⟨haD, by
      change D a ∈ hD.singularSet.branchCarrier c
      rwa [hay]⟩)
    refine mem_iUnion.mpr ⟨⟨a, haJ⟩, ?_⟩
    change (y : E) ∈ W ⟨a, haJ⟩
    exact congrArg Subtype.val hay ▸ haW ⟨a, haJ⟩
  obtain ⟨t, ht⟩ := (hD.singularSet.branchCarrier_isCompact c).elim_finite_subcover
    (fun a : J => Subtype.val ⁻¹' W a) (fun a => (hW a).preimage continuous_subtype_val) hcover
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
    (show IsPLBall 2 (P j.1.1 j.2) from ⟨q j.1.1 j.2, (hq j.1.1 j.2).1⟩).isPolyhedron
  have hPR₀ : ∀ j : t × Fin 4, P j.1.1 j.2 ⊆ R₀.space := by
    intro j x hx
    exact hR₀L.space_eq.symm ▸ ((hq j.1.1 j.2).2 hx).1
  obtain ⟨R, hRR₀, hRfin, hΓR, hPR, hcells⟩ :=
    exists_isSubdivision_derivedCells_subset_cover R₀ hΓpoly hΓR₀
      (fun j : t × Fin 4 => P j.1.1 j.2) hPpoly hPR₀
      (fun j : t => W j.1) (fun j => hW j.1) hcoverE
  refine ⟨t, R, fun j => ψ j.1, fun j => V j.1, fun j => Ω j.1, fun j => W j.1,
    fun j => A j.1, fun j => P j.1, fun j => q j.1, hRR₀, hRfin, hΓR, ?_, hcells⟩
  intro j
  refine ⟨hV j.1, hΩ j.1, hW j.1, hWΩ j.1, hψ j.1, hF j.1, hΓ j.1,
    hA j.1, hAA j.1, hpre j.1, hcore j.1, fun i => ?_⟩
  exact ⟨(hq j.1 i).1, (hq j.1 i).2, hPR (j, i), fun x hx =>
    ⟨hread j.1 x hx i, hsource j.1 x hx i, hbd j.1 x hx i⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
