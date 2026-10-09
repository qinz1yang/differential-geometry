/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedIntervalLink
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarFibers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_derived_collar_arm_parameters (hD : NormalSingularCellData D BdM B)
    {ι : M → E} (hι : Function.Injective ι) (hPL : IsPiecewiseAffineOn (ι ∘ D) D.domain)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (haR : {ι (D a)} ∈ R.faces)
    (hpos : (PiecewiseLinear.restrict R
      ((fun t : ℝ => ι (D (ρ (a, t)))) '' Icc 0 1)).space =
        (fun t : ℝ => ι (D (ρ (a, t)))) '' Icc 0 1)
    (hneg : (PiecewiseLinear.restrict R
      ((fun t : ℝ => ι (D (ρ (a, t)))) '' Icc (-1) 0)).space =
        (fun t : ℝ => ι (D (ρ (a, t)))) '' Icc (-1) 0) :
    ∃ vP ∈ Ioc (0 : ℝ) 1, ∃ vM ∈ Ico (-1 : ℝ) 0,
      (derivedNeighborhoodCellBase R {ι (D a)}).space ∩
        ((fun t : ℝ => ι (D (ρ (a, t)))) '' Icc 0 1) = {ι (D (ρ (a, vP)))} ∧
      (derivedNeighborhoodCellBase R {ι (D a)}).space ∩
        ((fun t : ℝ => ι (D (ρ (a, t)))) '' Icc (-1) 0) = {ι (D (ρ (a, vM)))} := by
  let F : ℝ → E := fun t => ι (D (ρ (a, t)))
  have hF := hD.isPLHomeomorphOn_collarFiber hι hPL hρ ha
  have hF0 : F 0 = ι (D a) := congrArg (ι ∘ D) (hρ.2.2.2.2.2.2.1 a ha)
  let AP := PiecewiseLinear.restrict R (F '' Icc 0 1)
  let AM := PiecewiseLinear.restrict R (F '' Icc (-1) 0)
  let _ : Finite AP.faces := (restrict_faces_finite R _).to_subtype
  let _ : Finite AM.faces := (restrict_faces_finite R _).to_subtype
  have hFP : IsPLHomeomorphOn F (Icc 0 1) AP.space := by
    rw [show AP.space = F '' Icc 0 1 from hpos]
    exact hF.restrict isHPolytope_Icc.isPolyhedron
      (Icc_subset_Icc (by norm_num) le_rfl)
  have hFM : IsPLHomeomorphOn F (Icc (-1) 0) AM.space := by
    rw [show AM.space = F '' Icc (-1) 0 from hneg]
    exact hF.restrict isHPolytope_Icc.isPolyhedron
      (Icc_subset_Icc le_rfl (by norm_num))
  obtain ⟨vP, hvP, hneP, hlinkP⟩ := exists_derived_interval_link_parameter R AP
    (restrict_faces_subset R _) (by norm_num : (0 : ℝ) < 1) hFP haR (Or.inl hF0.symm)
  obtain ⟨vM, hvM, hneM, hlinkM⟩ := exists_derived_interval_link_parameter R AM
    (restrict_faces_subset R _) (by norm_num : (-1 : ℝ) < 0) hFM haR (Or.inr hF0.symm)
  have hP : 0 < vP := lt_of_le_of_ne hvP.1 fun h => hneP ((congrArg F h.symm).trans hF0)
  have hM : vM < 0 := lt_of_le_of_ne hvM.2 fun h => hneM ((congrArg F h).trans hF0)
  exact ⟨vP, ⟨hP, hvP.2⟩, vM, ⟨hvM.1, hM⟩, by rwa [hpos] at hlinkP, by rwa [hneg] at hlinkM⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem collar_arm_inter_branchCarrier (hD : NormalSingularCellData D BdM B)
    {ι : M → E} (hι : Function.Injective ι)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) {I : Set ℝ}
    (hI : I ⊆ Icc (-1 : ℝ) 1) (h0 : (0 : ℝ) ∈ I) :
    ((fun t : ℝ => ι (D (ρ (a, t)))) '' I) ∩ ι '' hD.singularSet.branchCarrier c =
      {ι (D a)} := by
  have hρ0 : ρ (a, 0) = a := hρ.2.2.2.2.2.2.1 a ha
  ext y
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, z, hz, hzy⟩
    have heq : z = D (ρ (a, t)) := hι hzy
    have ht0 : t = 0 := (hD.mem_branchCarrier_collarFiber_iff hρ ha (hI ht)).mp (heq ▸ hz)
    change ι (D (ρ (a, t))) = ι (D a)
    rw [ht0, hρ0]
  · rintro rfl
    refine ⟨⟨0, h0, congrArg (ι ∘ D) hρ0⟩, D a, ?_, rfl⟩
    exact (show a ∈ hD.branchPreimage c from hρ.1.symm ▸ ha).2

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
