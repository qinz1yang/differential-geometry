/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem injOn_collarFiber (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) :
    InjOn (fun t : ℝ => D (ρ (a, t))) (Icc (-1 : ℝ) 1) := by
  intro t ht s hs heq
  by_cases ht0 : t = 0
  · by_cases hs0 : s = 0
    · exact ht0.trans hs0.symm
    · exact (hD.eq_of_apply_eq_of_isTwoSidedBranchCollar hρ ha hs hs0 ha ht heq.symm).2.symm
  · exact (hD.eq_of_apply_eq_of_isTwoSidedBranchCollar hρ ha ht ht0 ha hs heq).2

theorem mem_branchCarrier_collarFiber_iff (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    D (ρ (a, t)) ∈ hD.singularSet.branchCarrier c ↔ t = 0 := by
  obtain ⟨hpre, -, hCint, -, -, hρpl, hρ0, hdpp, -, -, -, -, -⟩ := hρ
  constructor
  · intro hmem
    have hxC : ρ (a, t) ∈ C := hρpl.bijOn.mapsTo ⟨ha, ht⟩
    have hxD := interior_subset (hCint hxC)
    have hxJ : ρ (a, t) ∈ J := hdpp.subset
      ⟨⟨hxD, hD.singularSet.branchCarrier_subset_doublePointSet c hmem⟩, hxC⟩
    have heq : (ρ (a, t), (0 : ℝ)) = (a, t) :=
      hρpl.bijOn.injOn ⟨hxJ, by constructor <;> norm_num⟩ ⟨ha, ht⟩ (hρ0 _ hxJ)
    exact (congrArg Prod.snd heq).symm
  · rintro rfl
    rw [hρ0 a ha]
    have hapre : a ∈ hD.branchPreimage c := hpre.symm ▸ ha
    exact hapre.2

theorem collarFiber_image_inter_of_ne (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a b : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b)
    (hDab : D a = D b) :
    (fun t : ℝ => D (ρ (a, t))) '' Icc (-1 : ℝ) 1 ∩
      (fun t : ℝ => D (ρ (b, t))) '' Icc (-1 : ℝ) 1 = {D a} := by
  have hρ0 := hρ.2.2.2.2.2.2.1
  ext y
  constructor
  · rintro ⟨⟨t, ht, hty⟩, ⟨s, hs, hsy⟩⟩
    have ht0 : t = 0 := by
      by_contra ht0
      exact hab (hD.eq_of_apply_eq_of_isTwoSidedBranchCollar hρ ha ht ht0 hb hs
        (hty.trans hsy.symm)).1
    change D (ρ (a, t)) = y at hty
    rw [ht0, hρ0 a ha] at hty
    exact hty.symm
  · rintro rfl
    have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
    exact ⟨⟨0, h0, congrArg D (hρ0 a ha)⟩,
      ⟨0, h0, (congrArg D (hρ0 b hb)).trans hDab.symm⟩⟩

theorem isPLHomeomorphOn_collarFiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hD : NormalSingularCellData D BdM B) {ι : M → E} (hι : Function.Injective ι)
    (hPL : IsPiecewiseAffineOn (ι ∘ D) D.domain)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) :
    IsPLHomeomorphOn (fun t : ℝ => ι (D (ρ (a, t)))) (Icc (-1 : ℝ) 1)
      ((fun t : ℝ => ι (D (ρ (a, t)))) '' Icc (-1 : ℝ) 1) := by
  obtain ⟨-, -, hCint, -, -, hρpl, -, -, -, -, -, -, -⟩ := id hρ
  let A : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) × ℝ :=
    (AffineMap.const ℝ ℝ a).prod (AffineMap.id ℝ ℝ)
  have hA : IsPiecewiseAffineOn A (Icc (-1 : ℝ) 1) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope A isHPolytope_Icc
  have hAmaps : MapsTo A (Icc (-1 : ℝ) 1) (J ×ˢ Icc (-1 : ℝ) 1) :=
    fun t ht => ⟨ha, ht⟩
  have hρA : IsPiecewiseAffineOn (fun t => ρ (a, t)) (Icc (-1 : ℝ) 1) := by
    exact (hρpl.isPiecewiseAffineOn.comp hA).mono_of_isPolyhedron
      isHPolytope_Icc.isPolyhedron (fun t ht => ⟨ht, hAmaps ht⟩)
  have hmaps : MapsTo (fun t => ρ (a, t)) (Icc (-1 : ℝ) 1) D.domain :=
    fun t ht => interior_subset (hCint (hρpl.bijOn.mapsTo ⟨ha, ht⟩))
  have hf : IsPiecewiseAffineOn (fun t => ι (D (ρ (a, t)))) (Icc (-1 : ℝ) 1) := by
    exact (hPL.comp hρA).mono_of_isPolyhedron
      isHPolytope_Icc.isPolyhedron (fun t ht => ⟨ht, hmaps ht⟩)
  have hinj : InjOn (fun t => ι (D (ρ (a, t)))) (Icc (-1 : ℝ) 1) :=
    fun t ht s hs heq => hD.injOn_collarFiber hρ ha ht hs (hι heq)
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron hf
    hinj.bijOn_image

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
