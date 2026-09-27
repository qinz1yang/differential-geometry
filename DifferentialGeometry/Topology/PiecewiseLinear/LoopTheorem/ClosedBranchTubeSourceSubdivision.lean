/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarFibers
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTubeCarrier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_subdivision_branchCarrier_collarArms
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
        {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)},
        hD.IsTwoSidedBranchCollar c J Q C ρ →
        ∀ (a : Bool → EuclideanSpace ℝ (Fin 2)), (∀ b, a b ∈ J) →
          ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R L ∧ R.faces.Finite ∧
            ({((D (a false) : L.space) : E)} : Finset E) ∈ R.faces ∧
            (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space =
              Subtype.val '' hD.singularSet.branchCarrier c ∧
            IsCombinatorialManifold 1
              (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)) ∧
            IsConnected
              (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space ∧
            (PiecewiseLinear.restrict R (Subtype.val '' (D '' D.domain))).space =
              Subtype.val '' (D '' D.domain) ∧
            ∀ b σ : Bool,
              (PiecewiseLinear.restrict R
                ((fun t : ℝ => ((D (ρ (a b, t)) : L.space) : E)) ''
                  (if σ then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0))).space =
                (fun t : ℝ => ((D (ρ (a b, t)) : L.space) : E)) ''
                  (if σ then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0) := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J Q C ρ hρ a ha
  let F : Bool → ℝ → E := fun b t => ((D (ρ (a b, t)) : L.space) : E)
  let I : Bool → Set ℝ := fun σ => if σ then Icc 0 1 else Icc (-1) 0
  have hPL : IsPiecewiseAffineOn (Subtype.val ∘ D) D.domain :=
    isPiecewiseAffineOn_val_comp_of_isPLOn L hL D.domain D.toFun D.isPLOn
  have hF : ∀ b, IsPLHomeomorphOn (F b) (Icc (-1 : ℝ) 1)
      (F b '' Icc (-1 : ℝ) 1) := fun b =>
    hD.isPLHomeomorphOn_collarFiber Subtype.val_injective hPL hρ (ha b)
  have hI : ∀ σ, IsPolyhedron (I σ) := by
    intro σ
    cases σ <;> exact isHPolytope_Icc.isPolyhedron
  have hIsub : ∀ σ, I σ ⊆ Icc (-1 : ℝ) 1 := by
    intro σ t ht
    cases σ
    · exact ⟨ht.1, ht.2.trans zero_le_one⟩
    · exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans ht.1, ht.2⟩
  have hFpoly : ∀ b σ, IsPolyhedron (F b '' I σ) := fun b σ =>
    ((hF b).isPiecewiseAffineOn.mono_of_isPolyhedron (hI σ) (hIsub σ)).isPolyhedron_image (hI σ)
  have hΓ := isPLSphere_one_val_image_branchCarrier L hL D BdM hD.singularSet c hc
  let P : Bool ⊕ (Bool × Bool) → Set E := Sum.elim
    (fun b => if b then Subtype.val '' (D '' D.domain)
      else Subtype.val '' hD.singularSet.branchCarrier c)
    (fun b => F b.1 '' I b.2)
  have hPpoly : ∀ i, IsPolyhedron (P i) := by
    intro i
    rcases i with b | ⟨b, σ⟩
    · cases b
      · exact hΓ.isPolyhedron
      · exact SingularTwoCell.isPolyhedron_val_image L hL D
    · exact hFpoly b σ
  have hPLspace : ∀ i, P i ⊆ L.space := by
    intro i
    rcases i with b | ⟨b, σ⟩
    · cases b <;> rintro x ⟨y, -, rfl⟩ <;> exact y.2
    · rintro x ⟨t, -, rfl⟩
      exact (D (ρ (a b, t))).2
  obtain ⟨R₀, hR₀L, hR₀fin, hyR₀⟩ :=
    exists_isSubdivision_singleton_mem L (D (a false)).2
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  obtain ⟨R, hRR₀, hRfin, hPR⟩ := exists_isSubdivision_subcomplexes R₀ P hPpoly
    (fun i => hR₀L.space_eq.symm ▸ hPLspace i)
  have hPspace : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i :=
    fun i => restrict_space_of_eq_biUnion R (P i) (hPR i)
  have hΓspace :
      (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space =
        Subtype.val '' hD.singularSet.branchCarrier c := hPspace (Sum.inl false)
  have hΓR : IsPLSphere 1
      (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space := by
    rw [hΓspace]
    exact hΓ
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (PiecewiseLinear.restrict R
      (Subtype.val '' hD.singularSet.branchCarrier c)).faces :=
    (restrict_faces_finite R _).to_subtype
  exact ⟨R, hRR₀.trans hR₀L, hRfin, hRR₀.singleton_mem hyR₀, hΓspace,
    IsPLSphere.isCombinatorialManifold (n := 0) hΓR, hΓR.isConnected,
    hPspace (Sum.inl true), fun b σ => hPspace (Sum.inr (b, σ))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
