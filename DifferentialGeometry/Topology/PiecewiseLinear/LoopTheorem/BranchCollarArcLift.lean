/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarCoordinates

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [TopologicalSpace E] [T2Space E]

theorem exists_collar_lift_arc_in_source_sheet (hD : NormalSingularCellData D BdM B)
    {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {c : hD.singularSet.Branch} {J Q C A₀ A₁ : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    (hA₀ : IsCompact A₀) (hA₁ : IsCompact A₁) (hA₀C : A₀ ⊆ C) (hA₁C : A₁ ⊆ C)
    (hAA : Disjoint A₀ A₁) (hinj₀ : InjOn D A₀) (hinj₁ : InjOn D A₁)
    {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1))
    (hcover : γ '' Icc 0 1 ⊆ (ι ∘ D) '' A₀ ∪ (ι ∘ D) '' A₁)
    (hcore : ∀ t ∈ Icc (0 : ℝ) 1,
      γ t ∈ ι '' hD.singularSet.branchCarrier c ↔ t = 0 ∨ t = 1) :
    ∃ (b : Bool) (ℓ : ℝ → EuclideanSpace ℝ (Fin 2) × ℝ),
      ContinuousOn ℓ (Icc 0 1) ∧ MapsTo ℓ (Icc 0 1) (J ×ˢ Icc (-1 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ρ (ℓ t) ∈ (if b then A₁ else A₀) ∧
        ι (D (ρ (ℓ t))) = γ t) ∧
      (ℓ 0).2 = 0 ∧ (ℓ 1).2 = 0 ∧
      ((∀ t ∈ Ioo (0 : ℝ) 1, 0 < (ℓ t).2) ∨
        ∀ t ∈ Ioo (0 : ℝ) 1, (ℓ t).2 < 0) := by
  let f := ι ∘ D
  have hCdom : C ⊆ D.domain := hρ.2.2.1.trans interior_subset
  have hf : ContinuousOn f D.domain := hιc.comp_continuousOn D.continuousOn
  have hclosed₀ : IsClosed (f '' A₀) :=
    (hA₀.image_of_continuousOn (hf.mono (hA₀C.trans hCdom))).isClosed
  have hclosed₁ : IsClosed (f '' A₁) :=
    (hA₁.image_of_continuousOn (hf.mono (hA₁C.trans hCdom))).isClosed
  have hinter : f '' A₀ ∩ f '' A₁ ⊆ ι '' hD.singularSet.branchCarrier c := by
    rintro y ⟨⟨x, hx, hxy⟩, z, hz, hzy⟩
    have hDxz : D x = D z := hι (hxy.trans hzy.symm)
    have hxD : x ∈ D.domain := hCdom (hA₀C hx)
    have hzD : z ∈ D.domain := hCdom (hA₁C hz)
    have hxz : x ≠ z := fun h => disjoint_left.mp hAA hx (h.symm ▸ hz)
    have hxJ : x ∈ J := hρ.2.2.2.2.2.2.2.1.subset
      ⟨⟨hxD, x, hxD, z, hzD, hxz, rfl, hDxz.symm⟩, hA₀C hx⟩
    exact ⟨D x, (show x ∈ hD.branchPreimage c from hρ.1.symm ▸ hxJ).2, hxy⟩
  let U := γ '' Ioo (0 : ℝ) 1
  have hUcover : U ⊆ f '' A₀ ∪ f '' A₁ :=
    (image_mono Ioo_subset_Icc_self).trans hcover
  have hUconn : IsPreconnected U :=
    isPreconnected_Ioo.image γ (hγ.mono Ioo_subset_Icc_self)
  have hUno : Disjoint U (ι '' hD.singularSet.branchCarrier c) := by
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hmem
    rcases (hcore t (Ioo_subset_Icc_self ht)).mp hmem with h | h
    · exact ht.1.ne' h
    · exact ht.2.ne h
  have hsheet : ∃ b : Bool, U ⊆ f '' (if b then A₁ else A₀) := by
    by_cases hleft : U ⊆ f '' A₀
    · exact ⟨false, hleft⟩
    · obtain ⟨x, hx, hx₀⟩ := not_subset.mp hleft
      have hx₁ := (hUcover hx).resolve_left hx₀
      refine ⟨true, fun y hy => ?_⟩
      by_contra hy₁
      have hy₀ := (hUcover hy).resolve_right hy₁
      obtain ⟨z, hzU, hz₀, hz₁⟩ := isPreconnected_closed_iff.mp hUconn _ _
        hclosed₀ hclosed₁ hUcover ⟨y, hy, hy₀⟩ ⟨x, hx, hx₁⟩
      exact disjoint_left.mp hUno hzU (hinter ⟨hz₀, hz₁⟩)
  obtain ⟨b, hb⟩ := hsheet
  let A := if b then A₁ else A₀
  have hAc : IsCompact A := by cases b <;> assumption
  have hAC : A ⊆ C := by cases b <;> assumption
  have hfinj : InjOn f A := by
    intro x hx y hy hxy
    cases b
    · exact hinj₀ hx hy (hι hxy)
    · exact hinj₁ hx hy (hι hxy)
  have hfA := hf.mono (hAC.trans hCdom)
  have himageclosed : IsClosed (f '' A) := (hAc.image_of_continuousOn hfA).isClosed
  have hγfull : γ '' Icc (0 : ℝ) 1 ⊆ f '' A := by
    have hcl : γ '' closure (Ioo (0 : ℝ) 1) ⊆ closure U :=
      ContinuousOn.image_closure (by rwa [closure_Ioo zero_ne_one])
    rw [closure_Ioo zero_ne_one] at hcl
    exact hcl.trans (closure_minimal hb himageclosed)
  let v : ℝ → EuclideanSpace ℝ (Fin 2) := Function.invFunOn f A ∘ γ
  have hvmem : ∀ t ∈ Icc (0 : ℝ) 1, v t ∈ A :=
    fun t ht => Function.invFunOn_mem (hγfull ⟨t, ht, rfl⟩)
  have hvmap : ∀ t ∈ Icc (0 : ℝ) 1, f (v t) = γ t :=
    fun t ht => Function.invFunOn_eq (hγfull ⟨t, ht, rfl⟩)
  have hvc : ContinuousOn v (Icc 0 1) :=
    (continuousOn_invFunOn_of_isCompact_of_forall_eq hAc hfA (Subset.refl _)
      (fun x hx y hy hxy _ => hfinj hx hy hxy)).comp hγ
        (fun t ht => hγfull ⟨t, ht, rfl⟩)
  let ℓ := Function.invFunOn ρ (J ×ˢ Icc (-1 : ℝ) 1) ∘ v
  have hρpl := hρ.2.2.2.2.2.1
  have hℓc : ContinuousOn ℓ (Icc 0 1) :=
    hρpl.symm.isPiecewiseAffineOn.continuousOn.comp hvc (fun t ht => hAC (hvmem t ht))
  have hℓmem : MapsTo ℓ (Icc 0 1) (J ×ˢ Icc (-1 : ℝ) 1) :=
    fun t ht => hρpl.symm.bijOn.mapsTo (hAC (hvmem t ht))
  have hρℓ : ∀ t ∈ Icc (0 : ℝ) 1, ρ (ℓ t) = v t :=
    fun t ht => hρpl.bijOn.invOn_invFunOn.2 (hAC (hvmem t ht))
  have hmap : ∀ t ∈ Icc (0 : ℝ) 1, ι (D (ρ (ℓ t))) = γ t := by
    intro t ht
    rw [hρℓ t ht]
    exact hvmap t ht
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, (ℓ t).2 = 0 ↔ t = 0 ∨ t = 1 := by
    intro t ht
    have hmem := hℓmem ht
    rw [← hcore t ht, ← hmap t ht, hι.mem_set_image]
    exact (hD.mem_branchCarrier_collarFiber_iff hρ hmem.1 hmem.2).symm
  have hne : ∀ t ∈ Ioo (0 : ℝ) 1, (ℓ t).2 ≠ 0 := by
    intro t ht hz
    rcases (hzero t (Ioo_subset_Icc_self ht)).mp hz with h | h
    · exact ht.1.ne' h
    · exact ht.2.ne h
  refine ⟨b, ℓ, hℓc, hℓmem, fun t ht => ⟨?_, hmap t ht⟩,
    (hzero 0 ⟨le_rfl, zero_le_one⟩).mpr (Or.inl rfl),
    (hzero 1 ⟨zero_le_one, le_rfl⟩).mpr (Or.inr rfl), ?_⟩
  · rw [hρℓ t ht]
    exact hvmem t ht
  · have hmid : (1 / 2 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
    rcases lt_or_gt_of_ne (hne _ hmid) with hneg | hpos
    · exact Or.inr (neg_of_isPreconnected_of_ne_zero isPreconnected_Ioo
        (hℓc.snd.mono Ioo_subset_Icc_self) hne hmid hneg)
    · exact Or.inl (pos_of_isPreconnected_of_ne_zero isPreconnected_Ioo
        (hℓc.snd.mono Ioo_subset_Icc_self) hne hmid hpos)

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
