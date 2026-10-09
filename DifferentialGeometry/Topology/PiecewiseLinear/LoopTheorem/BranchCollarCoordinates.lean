/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarFibers
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubeTransverse

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_open_branchCarrier_preimage_subset_collar (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) :
    ∃ U : Set M, IsOpen U ∧ hD.singularSet.branchCarrier c ⊆ U ∧
      D.domain ∩ D ⁻¹' U ⊆ interior C := by
  have hclosed : IsClosed (D '' (D.domain \ interior C)) :=
    ((D.isPLBall_domain.isPolyhedron.isCompact.diff isOpen_interior).image_of_continuousOn
      (D.continuousOn.mono sdiff_subset)).isClosed
  refine ⟨(D '' (D.domain \ interior C))ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · intro y hy
    rintro ⟨x, ⟨hxD, hxC⟩, hxy⟩
    have hxpre : x ∈ hD.branchPreimage c := ⟨hxD, by
      change D x ∈ hD.singularSet.branchCarrier c
      rwa [hxy]⟩
    have hxJ : x ∈ J := hρ.1 ▸ hxpre
    exact hxC (mem_interior_iff_mem_nhds.mpr (hρ.2.2.2.2.1 x hxJ))
  · rintro x ⟨hxD, hxU⟩
    by_contra hxC
    exact hxU ⟨x, ⟨hxD, hxC⟩, rfl⟩

omit [T2Space M] in
theorem invFunOn_branchCollar_apply (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (ht0 : t ≠ 0) :
    Function.invFunOn (D ∘ ρ) (J ×ˢ Icc (-1 : ℝ) 1) (D (ρ (a, t))) = (a, t) := by
  have hex : ∃ p ∈ J ×ˢ Icc (-1 : ℝ) 1, (D ∘ ρ) p = D (ρ (a, t)) :=
    ⟨(a, t), ⟨ha, ht⟩, rfl⟩
  have hmem := Function.invFunOn_mem hex
  have heq := Function.invFunOn_eq hex
  have h := hD.eq_of_apply_eq_of_isTwoSidedBranchCollar hρ ha ht ht0
    hmem.1 hmem.2 heq.symm
  exact Prod.ext h.1.symm h.2.symm

theorem continuousOn_invFunOn_branchCollar (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsCompact J) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) :
    ContinuousOn (Function.invFunOn (D ∘ ρ) (J ×ˢ Icc (-1 : ℝ) 1))
      (D '' C \ hD.singularSet.branchCarrier c) := by
  have hρpl := hρ.2.2.2.2.2.1
  have hCdom : C ⊆ D.domain := hρ.2.2.1.trans interior_subset
  have hf : ContinuousOn (D ∘ ρ) (J ×ˢ Icc (-1 : ℝ) 1) :=
    D.continuousOn.comp hρpl.isPiecewiseAffineOn.continuousOn
      (fun p hp => hCdom (hρpl.bijOn.mapsTo hp))
  apply continuousOn_invFunOn_of_isCompact_of_forall_eq (hJ.prod isCompact_Icc) hf
  · intro y hy
    obtain ⟨x, hxC, hxy⟩ := hy.1
    obtain ⟨p, hp, hpx⟩ := hρpl.bijOn.surjOn hxC
    exact ⟨p, hp, (congrArg D hpx).trans hxy⟩
  · intro p hp q hq hpq hpW
    have hp0 : p.2 ≠ 0 := by
      intro hp0
      exact hpW.2 ((hD.mem_branchCarrier_collarFiber_iff hρ hp.1 hp.2).mpr hp0)
    have heq := hD.eq_of_apply_eq_of_isTwoSidedBranchCollar hρ hp.1 hp.2 hp0 hq.1 hq.2 hpq
    exact Prod.ext heq.1 heq.2

omit [T2Space M] in
theorem invFunOn_branchCollar_mem (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) {y : M}
    (hy : y ∈ D '' C \ hD.singularSet.branchCarrier c) :
    let p := Function.invFunOn (D ∘ ρ) (J ×ˢ Icc (-1 : ℝ) 1) y
    p ∈ J ×ˢ Icc (-1 : ℝ) 1 ∧ p.2 ≠ 0 ∧ D (ρ p) = y := by
  dsimp only
  obtain ⟨x, hxC, hxy⟩ := hy.1
  obtain ⟨p, hp, hpx⟩ := hρ.2.2.2.2.2.1.bijOn.surjOn hxC
  have hf : (D ∘ ρ) p = y := (congrArg D hpx).trans hxy
  have hp0 : p.2 ≠ 0 := by
    intro hp0
    exact hy.2 (hf ▸ (hD.mem_branchCarrier_collarFiber_iff hρ hp.1 hp.2).mpr hp0)
  have hinv : Function.invFunOn (D ∘ ρ) (J ×ˢ Icc (-1 : ℝ) 1) y = p := by
    rw [← hf]
    exact hD.invFunOn_branchCollar_apply hρ hp.1 hp.2 hp0
  rw [hinv]
  exact ⟨hp, hp0, hf⟩

theorem collar_side_eq_of_isPreconnected (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsCompact J) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {U : Set M} (hU : U ⊆ D '' C \ hD.singularSet.branchCarrier c)
    (hconn : IsPreconnected U) {a b : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) (hb : b ∈ J)
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsa : D (ρ (a, s)) ∈ U) (htb : D (ρ (b, t)) ∈ U) :
    (0 < s ↔ 0 < t) := by
  let v : M → ℝ := fun y => (Function.invFunOn (D ∘ ρ) (J ×ˢ Icc (-1 : ℝ) 1) y).2
  have hvc : ContinuousOn v U := (hD.continuousOn_invFunOn_branchCollar hJ hρ).snd.mono hU
  have hv0 : ∀ y ∈ U, v y ≠ 0 := fun y hy => (hD.invFunOn_branchCollar_mem hρ (hU hy)).2.1
  have hs0 : s ≠ 0 := fun h => (hU hsa).2
    ((hD.mem_branchCarrier_collarFiber_iff hρ ha hs).mpr h)
  have ht0 : t ≠ 0 := fun h => (hU htb).2
    ((hD.mem_branchCarrier_collarFiber_iff hρ hb ht).mpr h)
  have hvs : v (D (ρ (a, s))) = s :=
    congrArg Prod.snd (hD.invFunOn_branchCollar_apply hρ ha hs hs0)
  have hvt : v (D (ρ (b, t))) = t :=
    congrArg Prod.snd (hD.invFunOn_branchCollar_apply hρ hb ht ht0)
  constructor
  · intro hspos
    exact hvt ▸ pos_of_isPreconnected_of_ne_zero hconn hvc hv0 hsa (hvs.symm ▸ hspos) _ htb
  · intro htpos
    exact hvs ▸ pos_of_isPreconnected_of_ne_zero hconn hvc hv0 htb (hvt.symm ▸ htpos) _ hsa

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
