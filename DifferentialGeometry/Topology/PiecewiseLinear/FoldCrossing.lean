/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isPLHomeomorphOn_straighten_fold [FiniteDimensional ℝ E]
    {S T : Submodule ℝ E} (hcompl : IsCompl S T) {u v : E}
    (hu : u ∉ S) (hv : v ∉ S) (hnot : ∀ c : ℝ, 0 < c → v - c • u ∉ S) :
    ∃ (w : E) (h : E → E), w ∈ T ∧ w ≠ 0 ∧ u - w ∈ S ∧
      IsPLHomeomorphOn h univ univ ∧ EqOn h id (S : Set E) ∧
      h '' (T : Set E) = (T : Set E) ∧
      h '' ({y | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ y = s + r • u} ∪
        {y | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ y = s + r • v}) =
          (S ⊔ Submodule.span ℝ {w} : Submodule ℝ E) := by
  have hdecomp : ∀ z : E, ∃ s ∈ S, ∃ t ∈ T, s + t = z := by
    intro z
    apply Submodule.mem_sup.mp
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨s, hs, w, hwT, hsw⟩ := hdecomp u
  obtain ⟨t, ht, z, hzT, htz⟩ := hdecomp v
  have huw : u - w ∈ S := by simpa only [← hsw, add_sub_cancel_right] using hs
  have hvz : v - z ∈ S := by simpa only [← htz, add_sub_cancel_right] using ht
  have hw : w ≠ 0 := by
    intro hw0
    apply hu
    simpa only [hw0, sub_zero] using huw
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    simpa only [hz0, sub_zero] using hvz
  have hn : ∀ c : ℝ, 0 < c → z ≠ c • w := by
    intro c hc hzw
    apply hnot c hc
    have heq : v - c • u = (v - z) - c • (u - w) := by
      rw [hzw]
      module
    rw [heq]
    exact S.sub_mem hvz (S.smul_mem c huw)
  obtain ⟨h, hh, hfix, hT, hfold⟩ :=
    exists_isPLHomeomorphOn_straighten_two_halfSpaces hcompl.disjoint hwT hzT hw hz hn
  refine ⟨w, h, hwT, hw, huw, hh, hfix, hT, ?_⟩
  rw [halfSpace_eq_of_sub_mem S huw, halfSpace_eq_of_sub_mem S hvz]
  exact hfold

theorem hasPLCrossingAt_of_fold [FiniteDimensional ℝ E]
    {S T : Submodule ℝ E} (hSdim : Module.finrank ℝ S = 1)
    (hTdim : Module.finrank ℝ T = 2) (hcompl : IsCompl S T) {u v x : E}
    (hu : u ∉ S) (hv : v ∉ S) (hnot : ∀ c : ℝ, 0 < c → v - c • u ∉ S)
    {A B : Set E}
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔
      (∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ y - x = s + r • u) ∨
        ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ y - x = s + r • v)
    (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ y - x ∈ T) :
    HasPLCrossingAt A B x := by
  obtain ⟨w, f, hwT, hw, _, hf, hfix, hT, hfold⟩ :=
    exists_isPLHomeomorphOn_straighten_fold hcompl hu hv hnot
  let P : Submodule ℝ E := S ⊔ Submodule.span ℝ {w}
  have hwS : w ∉ S := fun hwS => hw (Submodule.disjoint_def.mp hcompl.disjoint _ hwS hwT)
  have hspan : Module.finrank ℝ (Submodule.span ℝ ({w} : Set E)) = 1 :=
    finrank_span_singleton hw
  have hI0 : Module.finrank ℝ (S ⊓ Submodule.span ℝ {w} : Submodule ℝ E) = 0 :=
    Submodule.finrank_eq_zero.mpr (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem
        hwS))
  have hPdim : Module.finrank ℝ P = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℝ {w})
    change Module.finrank ℝ P + _ = _ at h
    omega
  have hPT : P ⊔ T = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top]
    exact sup_le_sup le_sup_left le_rfl
  have hdim : Module.finrank ℝ E = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S T
    rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot] at h
    omega
  have hIdim : Module.finrank ℝ (P ⊓ T : Submodule ℝ E) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P T
    rw [hPT, finrank_top] at h
    omega
  have hfinj : Function.Injective f := fun a b hab =>
    hf.bijOn.injOn (mem_univ a) (mem_univ b) hab
  have hmem : ∀ (C : Set E) (y : E), f y ∈ f '' C ↔ y ∈ C := by
    intro C y
    exact hfinj.mem_set_image
  let h : E → E := fun y => f (y - x)
  have hh : IsPLHomeomorphOn h univ univ := by
    have hcomp := (isPLHomeomorphOn_add_const (-x)).trans hf
    apply hcomp.congr
    intro y _
    change f (y - x) = f (y + -x)
    rw [sub_eq_add_neg]
  have hhx : h x = 0 := by
    change f (x - x) = 0
    rw [sub_self]
    exact hfix S.zero_mem
  refine ⟨univ, univ, h, P, T, 0, 0, isOpen_univ, isOpen_univ, mem_univ x,
    hh, hhx, hPdim, hTdim, hIdim, hPT, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
  filter_upwards [hA, hB] with y hyA hyB
  simp only [LinearMap.zero_apply, le_refl, and_true]
  constructor
  · have hm := hmem ({z | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ z = s + r • u} ∪
        {z | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ z = s + r • v}) (y - x)
    rw [hfold] at hm
    exact hyA.trans hm.symm
  · have hm := hmem (T : Set E) (y - x)
    rw [hT] at hm
    exact hyB.trans hm.symm

end DifferentialGeometry.Topology.PiecewiseLinear
