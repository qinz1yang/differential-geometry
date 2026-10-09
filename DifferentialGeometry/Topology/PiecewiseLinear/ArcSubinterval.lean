/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_subarc_between_points {A : Set E} {η : ℝ → E}
    (hη : IsPLHomeomorphOn η (Icc 0 1) A) {p q : E} (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) :
    ∃ (C : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) C ∧
      γ 0 = p ∧ γ 1 = q ∧ C ⊆ A ∧
      (C = A → ({p, q} : Set E) = {η 0, η 1}) ∧ (η 0 ∈ C → η 1 ∈ C → C = A) := by
  have hordered : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      ∃ (C : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) C ∧
        γ 0 = η a ∧ γ 1 = η b ∧ C ⊆ A ∧
        (C = A → ({η a, η b} : Set E) = {η 0, η 1}) ∧
        (η 0 ∈ C → η 1 ∈ C → C = A) := by
    intro a b ha0 hab hb1
    let C := η '' Icc a b
    let γ := fun t : ℝ => η ((b - a) * t + a)
    have hγ : IsPLHomeomorphOn γ (Icc 0 1) C :=
      isPLHomeomorphOn_comp_mul_add_Icc hη ha0 hab hb1
    have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 hb1
    have hlimits : η 0 ∈ C → η 1 ∈ C → a = 0 ∧ b = 1 := by
      rintro ⟨u, hu, huη⟩ ⟨v, hv, hvη⟩
      have hu0 := hη.bijOn.injOn (hsub hu) (by norm_num) huη
      have hv1 := hη.bijOn.injOn (hsub hv) (by norm_num) hvη
      rw [hu0] at hu
      rw [hv1] at hv
      exact ⟨le_antisymm hu.1 ha0, le_antisymm hb1 hv.2⟩
    refine ⟨C, γ, hγ, ?_, ?_, (image_mono hsub).trans hη.image_eq.subset, ?_, ?_⟩
    · change η ((b - a) * 0 + a) = η a
      rw [mul_zero, zero_add]
    · change η ((b - a) * 1 + a) = η b
      rw [mul_one, sub_add_cancel]
    · intro hCA
      have h0C : η 0 ∈ C := hCA.symm ▸ hη.bijOn.mapsTo (by norm_num)
      have h1C : η 1 ∈ C := hCA.symm ▸ hη.bijOn.mapsTo (by norm_num)
      obtain ⟨ha, hb⟩ := hlimits h0C h1C
      rw [ha, hb]
    · intro h0C h1C
      obtain ⟨ha, hb⟩ := hlimits h0C h1C
      change η '' Icc a b = A
      rw [ha, hb, hη.image_eq]
  obtain ⟨a, ha, hηa⟩ := hη.bijOn.surjOn hp
  obtain ⟨b, hb, hηb⟩ := hη.bijOn.surjOn hq
  have hab : a ≠ b := fun h => hpq (hηa.symm.trans ((congrArg η h).trans hηb))
  rcases hab.lt_or_gt with hab | hba
  · obtain ⟨C, γ, hγ, hγ0, hγ1, hCA, hends, hfull⟩ := hordered a b ha.1 hab hb.2
    refine ⟨C, γ, hγ, hγ0.trans hηa, hγ1.trans hηb, hCA, ?_, hfull⟩
    intro h
    simpa only [hηa, hηb] using hends h
  · obtain ⟨C, γ, hγ, hγ0, hγ1, hCA, hends, hfull⟩ := hordered b a hb.1 hba ha.2
    refine ⟨C, fun t => γ (1 - t), isPLHomeomorphOn_comp_one_sub hγ, ?_, ?_, hCA, ?_, hfull⟩
    · simpa only [sub_zero] using hγ1.trans hηa
    · simpa only [sub_self] using hγ0.trans hηb
    · intro h
      exact (Set.pair_comm p q).trans (by simpa only [hηa, hηb] using hends h)

theorem exists_subarc_between_interior_points {A : Set E} {η : ℝ → E}
    (hη : IsPLHomeomorphOn η (Icc 0 1) A) {p q : E}
    (hp : p ∈ A \ {η 0, η 1}) (hq : q ∈ A \ {η 0, η 1}) (hpq : p ≠ q) :
    ∃ (C : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) C ∧
      γ 0 = p ∧ γ 1 = q ∧ C ⊆ A \ {η 0, η 1} := by
  have hordered : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      ∃ (C : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) C ∧
        γ 0 = η a ∧ γ 1 = η b ∧ C ⊆ A \ {η 0, η 1} := by
    intro a b ha hab hb
    have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha.le hb.le
    refine ⟨η '' Icc a b, fun t => η ((b - a) * t + a),
      isPLHomeomorphOn_comp_mul_add_Icc hη ha.le hab hb.le, ?_, ?_, ?_⟩
    · change η ((b - a) * 0 + a) = η a
      rw [mul_zero, zero_add]
    · change η ((b - a) * 1 + a) = η b
      rw [mul_one, sub_add_cancel]
    · rintro x ⟨t, ht, rfl⟩
      refine ⟨hη.bijOn.mapsTo (hsub ht), ?_⟩
      rintro (h0 | h1)
      · have ht0 := hη.bijOn.injOn (hsub ht) (by norm_num) h0
        exact (ha.trans_le ht.1).ne' ht0
      · have ht1 := hη.bijOn.injOn (hsub ht) (by norm_num) h1
        exact (ht.2.trans_lt hb).ne ht1
  obtain ⟨a, ha, hηa⟩ := hη.bijOn.surjOn hp.1
  obtain ⟨b, hb, hηb⟩ := hη.bijOn.surjOn hq.1
  have ha0 : 0 < a := lt_of_le_of_ne ha.1 (by
    intro h0
    exact hp.2 (Or.inl (hηa.symm.trans (congrArg η h0.symm))))
  have ha1 : a < 1 := lt_of_le_of_ne ha.2 (by
    intro h1
    exact hp.2 (Or.inr (hηa.symm.trans (congrArg η h1))))
  have hb0 : 0 < b := lt_of_le_of_ne hb.1 (by
    intro h0
    exact hq.2 (Or.inl (hηb.symm.trans (congrArg η h0.symm))))
  have hb1 : b < 1 := lt_of_le_of_ne hb.2 (by
    intro h1
    exact hq.2 (Or.inr (hηb.symm.trans (congrArg η h1))))
  have hab : a ≠ b := fun h => hpq (hηa.symm.trans ((congrArg η h).trans hηb))
  rcases hab.lt_or_gt with hab | hba
  · obtain ⟨C, γ, hγ, hγ0, hγ1, hC⟩ := hordered a b ha0 hab hb1
    exact ⟨C, γ, hγ, hγ0.trans hηa, hγ1.trans hηb, hC⟩
  · obtain ⟨C, γ, hγ, hγ0, hγ1, hC⟩ := hordered b a hb0 hba ha1
    refine ⟨C, fun t => γ (1 - t), isPLHomeomorphOn_comp_one_sub hγ, ?_, ?_, hC⟩
    · simpa only [sub_zero] using hγ1.trans hηa
    · simpa only [sub_self] using hγ0.trans hηb

end DifferentialGeometry.Topology.PiecewiseLinear
