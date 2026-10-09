/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TransversePlaneCoordinates
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

theorem exists_affineEquiv_prod_of_independent (hF : Module.finrank ℝ F = 3) {b₀ b₁ b₂ : F}
    (hb : ∀ α β γ : ℝ, α • b₀ + β • b₁ + γ • b₂ = 0 → α = 0 ∧ β = 0 ∧ γ = 0) (y : F) :
    ∃ A : F ≃ᵃ[ℝ] ℝ × ℝ × ℝ, ∀ α β γ : ℝ, A (y + (α • b₀ + β • b₁ + γ • b₂)) = (α, β, γ) := by
  let T : (ℝ × ℝ × ℝ) →ₗ[ℝ] F :=
    { toFun := fun p => p.1 • b₀ + p.2.1 • b₁ + p.2.2 • b₂
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h0, h1, h2⟩ := hb p.1 p.2.1 p.2.2 hp
    exact Prod.ext h0 (Prod.ext h1 h2)
  have hdim : Module.finrank ℝ (ℝ × ℝ × ℝ) = Module.finrank ℝ F := by
    rw [hF, Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Te : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] F := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  refine ⟨(AffineEquiv.vaddConst ℝ y).symm.trans Te.symm.toAffineEquiv, fun α β γ => ?_⟩
  have hT : Te (α, β, γ) = α • b₀ + β • b₁ + γ • b₂ := rfl
  simp only [AffineEquiv.trans_apply, AffineEquiv.vaddConst_symm_apply, vsub_eq_sub,
    add_sub_cancel_left, LinearEquiv.coe_toAffineEquiv]
  rw [← hT, LinearEquiv.symm_apply_apply]

theorem exists_affineEquiv_flatSheets (hE : Module.finrank ℝ E = 2)
    (hF : Module.finrank ℝ F = 3) {L₁ L₂ : E →ₗ[ℝ] F} (h₁ : Function.Injective L₁)
    (h₂ : Function.Injective L₂) {z : E} (hz : L₂ z ∉ LinearMap.range L₁) {ν : F →ₗ[ℝ] ℝ}
    (hν : ∃ ζ₁ ζ₂ : E, L₁ ζ₁ = L₂ ζ₂ ∧ ν (L₁ ζ₁) ≠ 0) (y : F) :
    ∃ (A : F ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (F₁ F₂ : E ≃ₗ[ℝ] ℝ × ℝ), (∀ q, (A q).2.2 = ν (q - y)) ∧
      (∀ ζ, A (y + L₁ ζ) = (0, (F₁ ζ).1, (F₁ ζ).2)) ∧
        ∀ ζ, A (y + L₂ ζ) = ((F₂ ζ).1, 0, (F₂ ζ).2) := by
  set P : Submodule ℝ F := LinearMap.range L₁ with hPdef
  set Q : Submodule ℝ F := LinearMap.range L₂ with hQdef
  have hP : Module.finrank ℝ P = 2 := by rw [LinearMap.finrank_range_of_inj h₁, hE]
  have hQ : Module.finrank ℝ Q = 2 := by rw [LinearMap.finrank_range_of_inj h₂, hE]
  have hlt : P < P ⊔ Q := by
    refine lt_of_le_of_ne le_sup_left fun h => hz ?_
    have hmem : L₂ z ∈ P ⊔ Q := Submodule.mem_sup_right (LinearMap.mem_range_self L₂ z)
    rw [← h] at hmem
    exact hmem
  have hsup : P ⊔ Q = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (P ⊔ Q)
    omega
  have hPQ : Module.finrank ℝ (P ⊓ Q : Submodule ℝ F) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hsup, finrank_top, hF, hP, hQ] at h
    omega
  have hone : ∃ u ∈ (P ⊓ Q : Submodule ℝ F), ν u = 1 := by
    obtain ⟨ζ₁, ζ₂, hζ, hne⟩ := hν
    exact exists_mem_apply_eq_one_of_exists_mem_apply_ne_zero
      ⟨L₁ ζ₁, ⟨LinearMap.mem_range_self L₁ ζ₁, hζ ▸ LinearMap.mem_range_self L₂ ζ₂⟩, hne⟩
  obtain ⟨L, hLP, hLQ, -, hLν⟩ :=
    exists_linearEquiv_of_transverse_planes_of_transverse_functional hP hQ hPQ hsup hone
  let rev : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ :=
    { toFun := fun p => (p.2.2, p.2.1, p.1)
      invFun := fun p => (p.2.2, p.2.1, p.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hdim2 : Module.finrank ℝ E = Module.finrank ℝ (ℝ × ℝ) := by
    rw [hE, Module.finrank_prod, Module.finrank_self]
  let G₁ : E →ₗ[ℝ] ℝ × ℝ :=
    (((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
      (L.toLinearMap.comp L₁)).prod ((LinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (L.toLinearMap.comp L₁))
  let G₂ : E →ₗ[ℝ] ℝ × ℝ :=
    (((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
      (L.toLinearMap.comp L₂)).prod ((LinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (L.toLinearMap.comp L₂))
  have hG₁ : ∀ ζ, G₁ ζ = ((L (L₁ ζ)).2.1, (L (L₁ ζ)).1) := fun _ => rfl
  have hG₂ : ∀ ζ, G₂ ζ = ((L (L₂ ζ)).2.2, (L (L₂ ζ)).1) := fun _ => rfl
  have hP0 : ∀ ζ, (L (L₁ ζ)).2.2 = 0 := fun ζ => (hLP _).mp (LinearMap.mem_range_self L₁ ζ)
  have hQ0 : ∀ ζ, (L (L₂ ζ)).2.1 = 0 := fun ζ => (hLQ _).mp (LinearMap.mem_range_self L₂ ζ)
  have hinj₁ : Function.Injective G₁ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ζ hζ
    rw [hG₁] at hζ
    have ha : (L (L₁ ζ)).2.1 = 0 := congrArg Prod.fst hζ
    have hb : (L (L₁ ζ)).1 = 0 := congrArg Prod.snd hζ
    have hL0 : L (L₁ ζ) = 0 := Prod.ext hb (Prod.ext ha (hP0 ζ))
    exact h₁ (by rw [L.map_eq_zero_iff.mp hL0, map_zero])
  have hinj₂ : Function.Injective G₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ζ hζ
    rw [hG₂] at hζ
    have ha : (L (L₂ ζ)).2.2 = 0 := congrArg Prod.fst hζ
    have hb : (L (L₂ ζ)).1 = 0 := congrArg Prod.snd hζ
    have hL0 : L (L₂ ζ) = 0 := Prod.ext hb (Prod.ext (hQ0 ζ) ha)
    exact h₂ (by rw [L.map_eq_zero_iff.mp hL0, map_zero])
  let F₁ : E ≃ₗ[ℝ] ℝ × ℝ := LinearEquiv.ofBijective G₁
    ⟨hinj₁, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hinj₁⟩
  let F₂ : E ≃ₗ[ℝ] ℝ × ℝ := LinearEquiv.ofBijective G₂
    ⟨hinj₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hinj₂⟩
  let A : F ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
    (AffineEquiv.vaddConst ℝ y).symm.trans (L.trans rev).toAffineEquiv
  have hA : ∀ q, A q = ((L (q - y)).2.2, (L (q - y)).2.1, (L (q - y)).1) := fun _ => rfl
  refine ⟨A, F₁, F₂, fun q => by rw [hA, hLν], fun ζ => ?_, fun ζ => ?_⟩
  · rw [hA, add_sub_cancel_left, hP0]
    rfl
  · rw [hA, add_sub_cancel_left, hQ0]
    rfl

theorem exists_affineEquiv_bentSheet (hE : Module.finrank ℝ E = 2)
    (hF : Module.finrank ℝ F = 3) {L L₂ : E →ₗ[ℝ] F} (hL : Function.Injective L)
    (hL₂ : Function.Injective L₂) {e n : E}
    (hen : ∀ a b : ℝ, a • e + b • n = 0 → a = 0 ∧ b = 0) {w : F}
    (hw : w ∉ LinearMap.range L) (he : L e ∉ LinearMap.range L₂) (y : F) :
    ∃ (A : F ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (μ μ' : ℝ) (F₂ : E ≃ₗ[ℝ] ℝ × ℝ),
      (∀ s t : ℝ, A (y + (s • L e + t • L n + max t 0 • w)) =
        (max t 0, s - μ' * t - μ * max t 0, t)) ∧
        ∀ ζ, A (y + L₂ ζ) = ((F₂ ζ).1, 0, (F₂ ζ).2) := by
  let Ψ : E × ℝ →ₗ[ℝ] F := L₂.coprod (-((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (L e)))
  have hΨ : ∀ ζ m, Ψ (ζ, m) = L₂ ζ - m • L e := by
    intro ζ m
    simp only [Ψ, LinearMap.coprod_apply, LinearMap.neg_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, sub_eq_add_neg]
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨ζ, m⟩ h0
    rw [hΨ, sub_eq_zero] at h0
    by_cases hm : m = 0
    · rw [hm, zero_smul] at h0
      have hζ : ζ = 0 := hL₂ (by rw [h0, map_zero])
      rw [hζ, hm]
      rfl
    · exfalso
      apply he
      refine ⟨m⁻¹ • ζ, ?_⟩
      rw [map_smul, h0, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have hdim3 : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F := by
    rw [hF, Module.finrank_prod, hE, Module.finrank_self]
  have hΨsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim3).mp hΨinj
  obtain ⟨⟨ζu, μ⟩, hu⟩ := hΨsurj w
  obtain ⟨⟨ζt, μ'⟩, ht⟩ := hΨsurj (L n)
  rw [hΨ] at hu ht
  have hbu : L₂ ζu = w + μ • L e := by rw [← hu]; abel
  have hbt : L₂ ζt = L n + μ' • L e := by rw [← ht]; abel
  have hindep : ∀ α β γ : ℝ, α • L₂ ζu + β • L e + γ • L₂ ζt = 0 →
      α = 0 ∧ β = 0 ∧ γ = 0 := by
    intro α β γ h
    rw [hbu, hbt] at h
    have hα : α = 0 := by
      by_contra hα
      apply hw
      refine ⟨-α⁻¹ • ((α * μ + β + γ * μ') • e + γ • n), ?_⟩
      have h' : α • w = -((α * μ + β + γ * μ') • L e + γ • L n) := by
        rw [eq_neg_iff_add_eq_zero, ← h]
        module
      rw [map_smul, map_add, map_smul, map_smul, neg_smul, ← smul_neg, ← h', smul_smul,
        inv_mul_cancel₀ hα, one_smul]
    subst hα
    have h2 : L ((β + γ * μ') • e + γ • n) = 0 := by
      rw [map_add, map_smul, map_smul, ← h]
      module
    have h3 : (β + γ * μ') • e + γ • n = 0 := hL (by rw [h2, map_zero])
    obtain ⟨hb, hg⟩ := hen _ _ h3
    refine ⟨rfl, ?_, hg⟩
    rw [hg, zero_mul, add_zero] at hb
    exact hb
  obtain ⟨A, hA⟩ := exists_affineEquiv_prod_of_independent hF hindep y
  have hpair : ∀ a b : ℝ, a • ζu + b • ζt = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h' : a • L₂ ζu + (0 : ℝ) • L e + b • L₂ ζt = 0 := by
      rw [zero_smul, add_zero, ← map_smul, ← map_smul, ← map_add, h, map_zero]
    obtain ⟨ha, -, hb⟩ := hindep a 0 b h'
    exact ⟨ha, hb⟩
  let T₂ : (ℝ × ℝ) →ₗ[ℝ] E :=
    { toFun := fun p => p.1 • ζu + p.2 • ζt
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hT₂inj : Function.Injective T₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h0, h1⟩ := hpair p.1 p.2 hp
    exact Prod.ext h0 h1
  have hdim2 : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E := by
    rw [hE, Module.finrank_prod, Module.finrank_self]
  let T₂e : (ℝ × ℝ) ≃ₗ[ℝ] E := LinearEquiv.ofBijective T₂
    ⟨hT₂inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hT₂inj⟩
  refine ⟨A, μ, μ', T₂e.symm, fun s t => ?_, fun ζ => ?_⟩
  · have heq : s • L e + t • L n + max t 0 • w =
        max t 0 • L₂ ζu + (s - μ' * t - μ * max t 0) • L e + t • L₂ ζt := by
      rw [hbu, hbt]
      module
    rw [heq, hA]
  · have hζ : ζ = (T₂e.symm ζ).1 • ζu + (T₂e.symm ζ).2 • ζt := by
      have h := T₂e.apply_symm_apply ζ
      exact h.symm
    have heq : L₂ ζ = (T₂e.symm ζ).1 • L₂ ζu + (0 : ℝ) • L e + (T₂e.symm ζ).2 • L₂ ζt := by
      conv_lhs => rw [hζ]
      rw [map_add, map_smul, map_smul, zero_smul, add_zero]
    rw [heq, hA]

end DifferentialGeometry.Topology.PiecewiseLinear
