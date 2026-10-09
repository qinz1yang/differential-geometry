/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.BicollarNeighborhood
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.ChartTameNestedCells

open Set Metric Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem closedBallParam_image_norm_le {Y : Set E3} (φ : Y ≃ₜ closedBall (0 : E3) 1) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    IsTopologicalCell 3 (closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ}) ∧
      interior (closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ}) =
        closedBallParam φ '' {b | ‖(b : E3)‖ < ρ} ∧
      frontier (closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ}) =
        closedBallParam φ '' {b | ‖(b : E3)‖ = ρ} := by
  have hgc : Continuous (closedBallParam φ) := continuous_closedBallParam φ
  have hgi : Function.Injective (closedBallParam φ) := injective_closedBallParam φ
  have hmem : ∀ b : closedBall (0 : E3) 1, ρ • (b : E3) ∈ closedBall (0 : E3) 1 := by
    intro b
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hρ0.le]
    have := mem_closedBall_zero_iff.mp b.2
    nlinarith [norm_nonneg (b : E3)]
  let F : closedBall (0 : E3) 1 → E3 := fun b => closedBallParam φ ⟨ρ • (b : E3), hmem b⟩
  have hs : Continuous fun b : closedBall (0 : E3) 1 =>
      (⟨ρ • (b : E3), hmem b⟩ : closedBall (0 : E3) 1) :=
    by
      apply Continuous.subtype_mk
      fun_prop
  have hFc : Continuous F := hgc.comp hs
  have hFi : Function.Injective F := by
    intro b c hbc
    have h' : ρ • (b : E3) = ρ • (c : E3) := congrArg Subtype.val (hgi hbc)
    exact Subtype.ext ((smul_right_inj hρ0.ne').mp h')
  have hnormF : ∀ b : closedBall (0 : E3) 1, ‖ρ • (b : E3)‖ = ρ * ‖(b : E3)‖ := by
    intro b
    rw [norm_smul, Real.norm_of_nonneg hρ0.le]
  have hpre : ∀ b' : closedBall (0 : E3) 1, ‖(b' : E3)‖ ≤ ρ →
      ∃ b : closedBall (0 : E3) 1, F b = closedBallParam φ b' ∧
        ρ * ‖(b : E3)‖ = ‖(b' : E3)‖ := by
    intro b' hb'
    have hm : ρ⁻¹ • (b' : E3) ∈ closedBall (0 : E3) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ0.le),
        inv_mul_le_iff₀ hρ0, mul_one]
      exact hb'
    refine ⟨⟨ρ⁻¹ • (b' : E3), hm⟩, ?_, ?_⟩
    · change closedBallParam φ ⟨ρ • ρ⁻¹ • (b' : E3), _⟩ = closedBallParam φ b'
      congr 1
      exact Subtype.ext (smul_inv_smul₀ hρ0.ne' _)
    · change ρ * ‖ρ⁻¹ • (b' : E3)‖ = ‖(b' : E3)‖
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ0.le), ← mul_assoc,
        mul_inv_cancel₀ hρ0.ne', one_mul]
  have hball1 : ∀ b : closedBall (0 : E3) 1, ‖(b : E3)‖ ≤ 1 :=
    fun b => mem_closedBall_zero_iff.mp b.2
  have hR1 : range F = closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ} := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨⟨ρ • (b : E3), hmem b⟩, ?_, rfl⟩
      change ‖ρ • (b : E3)‖ ≤ ρ
      rw [hnormF]
      nlinarith [hball1 b, norm_nonneg (b : E3)]
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨b, hb, -⟩ := hpre b' hb'
      exact ⟨b, hb⟩
  have hR2 : F '' ((Subtype.val : closedBall (0 : E3) 1 → E3) ⁻¹' ball 0 1) =
      closedBallParam φ '' {b | ‖(b : E3)‖ < ρ} := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨ρ • (b : E3), hmem b⟩, ?_, rfl⟩
      change ‖ρ • (b : E3)‖ < ρ
      have hb1 : ‖(b : E3)‖ < 1 := mem_ball_zero_iff.mp hb
      rw [hnormF]
      nlinarith [norm_nonneg (b : E3)]
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨b, hb, hbn⟩ := hpre b' (le_of_lt hb')
      refine ⟨b, ?_, hb⟩
      change (b : E3) ∈ ball (0 : E3) 1
      rw [mem_ball_zero_iff]
      have hb'' : ‖(b' : E3)‖ < ρ := hb'
      nlinarith [norm_nonneg (b : E3)]
  have hR3 : F '' ((Subtype.val : closedBall (0 : E3) 1 → E3) ⁻¹' sphere 0 1) =
      closedBallParam φ '' {b | ‖(b : E3)‖ = ρ} := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨ρ • (b : E3), hmem b⟩, ?_, rfl⟩
      change ‖ρ • (b : E3)‖ = ρ
      have hb1 : ‖(b : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp hb
      rw [hnormF, hb1, mul_one]
    · rintro ⟨b', hb', rfl⟩
      have hb'' : ‖(b' : E3)‖ = ρ := hb'
      obtain ⟨b, hb, hbn⟩ := hpre b' hb''.le
      refine ⟨b, ?_, hb⟩
      change (b : E3) ∈ sphere (0 : E3) 1
      rw [mem_sphere_zero_iff_norm]
      rw [hb''] at hbn
      have := mul_left_cancel₀ hρ0.ne' (hbn.trans (mul_one ρ).symm)
      exact this
  have hcompact : CompactSpace (closedBall (0 : E3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hint : interior (range F) =
      F '' ((Subtype.val : closedBall (0 : E3) 1 → E3) ⁻¹' ball 0 1) := by
    have h := interior_range_eq_image_preimage_interior (isCompact_closedBall (0 : E3) 1) F hFc
      hFi
    rwa [interior_closedBall (0 : E3) one_ne_zero] at h
  have hclosed : IsClosed (range F) := (isCompact_range hFc).isClosed
  refine ⟨?_, ?_, ?_⟩
  · rw [← hR1]
    let f : closedBall (0 : E3) 1 → range F := fun b => ⟨F b, b, rfl⟩
    have hf : Function.Bijective f :=
      ⟨fun b c hbc => by
        have hval := congrArg Subtype.val hbc
        exact hFi hval, fun y => by
        obtain ⟨b, hb⟩ := y.2
        exact ⟨b, Subtype.ext hb⟩⟩
    exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
      (hFc.subtype_mk _)).symm⟩
  · rw [← hR1, hint, hR2]
  · rw [← hR1, hclosed.frontier_eq, hint, ← image_univ, ← image_sdiff hFi,
      univ_sdiff_preimage_ball, hR3]

theorem IsTopologicalCell.exists_nested_isSphericalShell_isBicollared {Y K : Set E3}
    (hY : IsTopologicalCell 3 Y) (hK : IsCompact K) (hKY : K ⊆ interior Y) :
    ∃ C₁ C₂ : Set E3, IsTopologicalCell 3 C₁ ∧ IsTopologicalCell 3 C₂ ∧ K ⊆ interior C₁ ∧
      C₁ ⊆ interior C₂ ∧ C₂ ⊆ interior Y ∧
      IsSphericalShell (closure (C₂ \ C₁)) (frontier C₁) (frontier C₂) ∧
      IsBicollared (frontier C₂) := by
  obtain ⟨φ⟩ := hY
  have hgc : Continuous (closedBallParam φ) := continuous_closedBallParam φ
  have hgi : Function.Injective (closedBallParam φ) := injective_closedBallParam φ
  have hcompact : CompactSpace (closedBall (0 : E3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hYint : interior Y =
      closedBallParam φ '' ((Subtype.val : closedBall (0 : E3) 1 → E3) ⁻¹' ball 0 1) :=
    interior_eq_image_of_homeomorphClosedBall φ
  have hlt1 : ∀ b : closedBall (0 : E3) 1, closedBallParam φ b ∈ interior Y →
      ‖(b : E3)‖ < 1 := by
    intro b hb
    rw [hYint] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    rw [← hgi hbb']
    exact mem_ball_zero_iff.mp hb'
  obtain ⟨r₀, hr₀0, hr₀1, hr₀⟩ : ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < 1 ∧
      ∀ b : closedBall (0 : E3) 1, closedBallParam φ b ∈ K → ‖(b : E3)‖ ≤ r₀ := by
    have hS : IsCompact (closedBallParam φ ⁻¹' K) := (hK.isClosed.preimage hgc).isCompact
    rcases (closedBallParam φ ⁻¹' K).eq_empty_or_nonempty with hempty | hne
    · refine ⟨0, le_rfl, one_pos, fun b hb => ?_⟩
      have hb' : b ∈ closedBallParam φ ⁻¹' K := hb
      rw [hempty] at hb'
      exact hb'.elim
    · obtain ⟨b₀, hb₀, hmax⟩ :=
        hS.exists_isMaxOn hne (continuous_subtype_val.norm).continuousOn
      exact ⟨‖(b₀ : E3)‖, norm_nonneg _, hlt1 b₀ (hKY hb₀), fun b hb => hmax hb⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = (3 * r₀ + 1) / 4 := ⟨_, rfl⟩
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = (r₀ + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (1 - r₀) / 8 := ⟨_, rfl⟩
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; linarith
  have hr₀ρ₁ : r₀ < ρ₁ := by rw [hρ₁]; linarith
  have hρ₁ρ₂ : ρ₁ < ρ₂ := by rw [hρ₁, hρ₂]; linarith
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂]; linarith
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  have hhi : ρ₂ * (1 + a) < 1 := by rw [hρ₂, ha]; nlinarith
  have hlo : ρ₁ < ρ₂ * (1 - a) := by rw [hρ₁, hρ₂, ha]; nlinarith
  obtain ⟨hC₁cell, hC₁int, hC₁fr⟩ := closedBallParam_image_norm_le φ hρ₁0 (by linarith)
  obtain ⟨hC₂cell, hC₂int, hC₂fr⟩ := closedBallParam_image_norm_le φ (by linarith) hρ₂1.le
  refine ⟨closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ₁},
    closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ₂}, hC₁cell, hC₂cell, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hyY := hKY hy
    rw [hYint] at hyY
    obtain ⟨b, -, rfl⟩ := hyY
    rw [hC₁int]
    exact ⟨b, lt_of_le_of_lt (hr₀ b hy) hr₀ρ₁, rfl⟩
  · rw [hC₂int]
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, lt_of_le_of_lt hb hρ₁ρ₂, rfl⟩
  · rw [hYint]
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, mem_ball_zero_iff.mpr (lt_of_le_of_lt hb hρ₂1), rfl⟩
  · have hAc : IsCompact {b : closedBall (0 : E3) 1 | ρ₁ ≤ ‖(b : E3)‖ ∧ ‖(b : E3)‖ ≤ ρ₂} :=
      ((isClosed_le continuous_const continuous_subtype_val.norm).inter
        (isClosed_le continuous_subtype_val.norm continuous_const)).isCompact
    have hXA : closure (closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ₂} \
        closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ₁}) =
          closedBallParam φ '' {b | ρ₁ ≤ ‖(b : E3)‖ ∧ ‖(b : E3)‖ ≤ ρ₂} := by
      apply Subset.antisymm
      · apply closure_minimal _ (hAc.image hgc).isClosed
        rintro _ ⟨⟨b, hb, rfl⟩, hb1⟩
        refine ⟨b, ⟨?_, hb⟩, rfl⟩
        by_contra hlt
        exact hb1 ⟨b, (not_le.mp hlt).le, rfl⟩
      · rintro _ ⟨b, ⟨hb1, hb2⟩, rfl⟩
        rcases hb1.lt_or_eq with hlt | heq
        · refine subset_closure ⟨⟨b, hb2, rfl⟩, ?_⟩
          rintro ⟨b', hb', hbb'⟩
          rw [hgi hbb'] at hb'
          have hb'' : ‖(b : E3)‖ ≤ ρ₁ := hb'
          linarith
        · have hfr : closedBallParam φ b ∈
              frontier (closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ₁}) := by
            rw [hC₁fr]
            exact ⟨b, heq.symm, rfl⟩
          have hint2 : closedBallParam φ b ∈
              interior (closedBallParam φ '' {b | ‖(b : E3)‖ ≤ ρ₂}) := by
            rw [hC₂int]
            refine ⟨b, ?_, rfl⟩
            change ‖(b : E3)‖ < ρ₂
            rw [← heq]
            exact hρ₁ρ₂
          have hcl := (frontier_eq_closure_inter_closure.subset hfr).2
          have hmem := isOpen_interior.inter_closure ⟨hint2, hcl⟩
          refine closure_mono ?_ hmem
          rintro z ⟨hz1, hz2⟩
          exact ⟨interior_subset hz1, hz2⟩
    rw [hXA, hC₁fr, hC₂fr]
    have hcoef0 : ∀ t : Icc (0 : ℝ) 1, 0 < ρ₁ + (t : ℝ) * (ρ₂ - ρ₁) := by
      intro t
      nlinarith [t.2.1]
    have hGnorm : ∀ p : sphere (0 : E3) 1 × Icc (0 : ℝ) 1,
        ‖(ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁)) • (p.1 : E3)‖ = ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁) := by
      intro p
      rw [norm_smul, mem_sphere_zero_iff_norm.mp p.1.2, mul_one,
        Real.norm_of_nonneg (hcoef0 p.2).le]
    have hmemG : ∀ p : sphere (0 : E3) 1 × Icc (0 : ℝ) 1,
        (ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁)) • (p.1 : E3) ∈ closedBall (0 : E3) 1 := by
      intro p
      rw [mem_closedBall_zero_iff, hGnorm p]
      nlinarith [p.2.2.1, p.2.2.2]
    let G : sphere (0 : E3) 1 × Icc (0 : ℝ) 1 → E3 := fun p =>
      closedBallParam φ ⟨(ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁)) • (p.1 : E3), hmemG p⟩
    have hGc : Continuous G := hgc.comp (by
      apply Continuous.subtype_mk
      fun_prop)
    have hGi : Function.Injective G := by
      intro p q hpq
      have hv := congrArg Subtype.val (hgi hpq)
      dsimp only at hv
      have hn := congrArg norm hv
      rw [hGnorm p, hGnorm q] at hn
      have ht : (p.2 : ℝ) = q.2 := by
        have hmul : (p.2 : ℝ) * (ρ₂ - ρ₁) = q.2 * (ρ₂ - ρ₁) := by linarith
        exact mul_right_cancel₀ (sub_ne_zero.mpr hρ₁ρ₂.ne') hmul
      rw [ht] at hv
      have hu : (p.1 : E3) = q.1 := (smul_right_inj (hcoef0 q.2).ne').mp hv
      exact Prod.ext (Subtype.ext hu) (Subtype.ext ht)
    have hGrange : range G = closedBallParam φ '' {b | ρ₁ ≤ ‖(b : E3)‖ ∧ ‖(b : E3)‖ ≤ ρ₂} := by
      ext y
      constructor
      · rintro ⟨p, rfl⟩
        refine ⟨⟨_, hmemG p⟩, ?_, rfl⟩
        change ρ₁ ≤ ‖(ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁)) • (p.1 : E3)‖ ∧
          ‖(ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁)) • (p.1 : E3)‖ ≤ ρ₂
        rw [hGnorm p]
        constructor <;> nlinarith [p.2.2.1, p.2.2.2]
      · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
        have hbpos : 0 < ‖(b : E3)‖ := lt_of_lt_of_le hρ₁0 hb1
        have hu : ‖(b : E3)‖⁻¹ • (b : E3) ∈ sphere (0 : E3) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.mpr hbpos.le), inv_mul_cancel₀ hbpos.ne']
        have ht : (‖(b : E3)‖ - ρ₁) / (ρ₂ - ρ₁) ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
        refine ⟨(⟨_, hu⟩, ⟨_, ht⟩), ?_⟩
        change closedBallParam φ ⟨_, _⟩ = closedBallParam φ b
        congr 1
        apply Subtype.ext
        change (ρ₁ + (‖(b : E3)‖ - ρ₁) / (ρ₂ - ρ₁) * (ρ₂ - ρ₁)) •
          (‖(b : E3)‖⁻¹ • (b : E3)) = b
        have hcoef : ρ₁ + (‖(b : E3)‖ - ρ₁) / (ρ₂ - ρ₁) * (ρ₂ - ρ₁) = ‖(b : E3)‖ := by
          rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hρ₁ρ₂.ne')]
          ring
        rw [hcoef, smul_inv_smul₀ hbpos.ne']
    have : CompactSpace (sphere (0 : E3) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
    have : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
    let f : sphere (0 : E3) 1 × Icc (0 : ℝ) 1 →
        closedBallParam φ '' {b | ρ₁ ≤ ‖(b : E3)‖ ∧ ‖(b : E3)‖ ≤ ρ₂} :=
      fun p => ⟨G p, hGrange ▸ mem_range_self p⟩
    have hf : Function.Bijective f := by
      refine ⟨fun p q hpq => ?_, fun y => ?_⟩
      · have hval := congrArg Subtype.val hpq
        exact hGi hval
      · have hy : (y : E3) ∈ range G := by
          rw [hGrange]
          exact y.2
        obtain ⟨p, hp⟩ := hy
        exact ⟨p, Subtype.ext hp⟩
    let Φ := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf) (hGc.subtype_mk _)
    have hΦ : ∀ T, Subtype.val '' (Φ '' T) = G '' T := by
      intro T
      rw [image_image]
      rfl
    have hend : ∀ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1),
        closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₁ + τ * (ρ₂ - ρ₁)} =
          G '' {p | (p.2 : ℝ) = τ} := by
      intro τ hτ
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        have hb' : ‖(b : E3)‖ = ρ₁ + τ * (ρ₂ - ρ₁) := hb
        have hbpos : 0 < ‖(b : E3)‖ := by rw [hb']; exact hcoef0 ⟨τ, hτ⟩
        have hu : ‖(b : E3)‖⁻¹ • (b : E3) ∈ sphere (0 : E3) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.mpr hbpos.le), inv_mul_cancel₀ hbpos.ne']
        refine ⟨(⟨_, hu⟩, ⟨τ, hτ⟩), rfl, ?_⟩
        change closedBallParam φ ⟨_, _⟩ = closedBallParam φ b
        congr 1
        apply Subtype.ext
        change (ρ₁ + τ * (ρ₂ - ρ₁)) • (‖(b : E3)‖⁻¹ • (b : E3)) = b
        rw [← hb', smul_inv_smul₀ hbpos.ne']
      · rintro ⟨p, hp, rfl⟩
        refine ⟨⟨_, hmemG p⟩, ?_, rfl⟩
        change ‖(ρ₁ + (p.2 : ℝ) * (ρ₂ - ρ₁)) • (p.1 : E3)‖ = ρ₁ + τ * (ρ₂ - ρ₁)
        rw [hGnorm p]
        have hp' : (p.2 : ℝ) = τ := hp
        rw [hp']
    refine ⟨Φ, ?_, ?_⟩
    · rw [hΦ, ← hend 0 ⟨le_rfl, zero_le_one⟩, zero_mul, add_zero]
    · rw [hΦ, ← hend 1 ⟨zero_le_one, le_rfl⟩, one_mul, add_sub_cancel]
  · rw [hC₂fr]
    have hF₂Y : ∀ x ∈ closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂}, x ∈ Y := by
      rintro _ ⟨b, -, rfl⟩
      exact (φ.symm b).2
    have hφg : ∀ b : closedBall (0 : E3) 1, φ ⟨closedBallParam φ b, (φ.symm b).2⟩ = b :=
      fun b => φ.apply_symm_apply b
    have hnormx : ∀ x : closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂},
        ‖((φ ⟨x.1, hF₂Y x.1 x.2⟩ : closedBall (0 : E3) 1) : E3)‖ = ρ₂ := by
      rintro ⟨_, b, hb, rfl⟩
      rw [show (φ ⟨closedBallParam φ b, hF₂Y _ ⟨b, hb, rfl⟩⟩ : closedBall (0 : E3) 1) = b from
        hφg b]
      exact hb
    have hF₂c : IsCompact (closedBallParam φ '' {b : closedBall (0 : E3) 1 | ‖(b : E3)‖ = ρ₂}) :=
      (isClosed_eq continuous_subtype_val.norm continuous_const).isCompact.image hgc
    have : CompactSpace (closedBallParam φ '' {b : closedBall (0 : E3) 1 | ‖(b : E3)‖ = ρ₂}) :=
      isCompact_iff_compactSpace.mp hF₂c
    have : CompactSpace (Icc (-a) a) := isCompact_iff_compactSpace.mp isCompact_Icc
    have hmemρ : ∀ q : (closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂}) × Icc (-a) a,
        (1 + (q.2 : ℝ)) • ((φ ⟨q.1.1, hF₂Y q.1.1 q.1.2⟩ : closedBall (0 : E3) 1) : E3) ∈
          closedBall (0 : E3) 1 := by
      intro q
      rw [mem_closedBall_zero_iff, norm_smul, hnormx q.1,
        Real.norm_of_nonneg (by linarith [q.2.2.1])]
      nlinarith [q.2.2.2]
    let ρc : (closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂}) × Icc (-a) a → E3 :=
      fun q => closedBallParam φ ⟨_, hmemρ q⟩
    have hφc : Continuous fun q : (closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂}) × Icc (-a) a =>
        ((φ ⟨q.1.1, hF₂Y q.1.1 q.1.2⟩ : closedBall (0 : E3) 1) : E3) :=
      continuous_subtype_val.comp
        (φ.continuous.comp ((continuous_subtype_val.comp continuous_fst).subtype_mk _))
    have hρcc : Continuous ρc := hgc.comp (by
      apply Continuous.subtype_mk
      exact (continuous_const.add (continuous_subtype_val.comp continuous_snd)).smul hφc)
    have hρci : Function.Injective ρc := by
      intro q r hqr
      have hv := congrArg Subtype.val (hgi hqr)
      dsimp only at hv
      have hn := congrArg norm hv
      rw [norm_smul, norm_smul, hnormx q.1, hnormx r.1,
        Real.norm_of_nonneg (by linarith [q.2.2.1]),
        Real.norm_of_nonneg (by linarith [r.2.2.1])] at hn
      have hs : (q.2 : ℝ) = r.2 := by
        have := mul_right_cancel₀ (by linarith : ρ₂ ≠ 0) hn
        linarith
      rw [hs] at hv
      have hb := (smul_right_inj (by linarith [r.2.2.1] : (1 + (r.2 : ℝ)) ≠ 0)).mp hv
      have hφeq := φ.injective (Subtype.ext hb)
      have h1 := congrArg Subtype.val hφeq
      exact Prod.ext (Subtype.ext h1) (Subtype.ext hs)
    have hzero : ∀ x : closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂},
        ρc (x, ⟨0, by constructor <;> linarith⟩) = (x : E3) := by
      rintro ⟨_, b, hb, rfl⟩
      change closedBallParam φ ⟨(1 + (0 : ℝ)) • _, _⟩ = closedBallParam φ b
      congr 1
      apply Subtype.ext
      change (1 + (0 : ℝ)) • ((φ ⟨closedBallParam φ b, _⟩ : closedBall (0 : E3) 1) : E3) = b
      rw [add_zero, one_smul,
        show (φ ⟨closedBallParam φ b, hF₂Y _ ⟨b, hb, rfl⟩⟩ : closedBall (0 : E3) 1) = b from
          hφg b]
    have hnbhd : range ρc ∈
        𝓝ˢ (range (Subtype.val : (closedBallParam φ '' {b | ‖(b : E3)‖ = ρ₂}) → E3)) := by
      rw [Subtype.range_coe, mem_nhdsSet_iff_forall]
      intro x hx
      have hρ₂0 : 0 < ρ₂ := by linarith
      obtain ⟨-, hIint, -⟩ := closedBallParam_image_norm_le φ
        (by positivity : 0 < ρ₂ * (1 + a)) hhi.le
      have hIc : IsClosed (closedBallParam φ '' {b : closedBall (0 : E3) 1 |
          ‖(b : E3)‖ ≤ ρ₂ * (1 - a)}) :=
        ((isClosed_le continuous_subtype_val.norm continuous_const).isCompact.image hgc).isClosed
      have hO : IsOpen (interior (closedBallParam φ '' {b : closedBall (0 : E3) 1 |
          ‖(b : E3)‖ ≤ ρ₂ * (1 + a)}) \
            closedBallParam φ '' {b : closedBall (0 : E3) 1 | ‖(b : E3)‖ ≤ ρ₂ * (1 - a)}) :=
        isOpen_interior.sdiff hIc
      have hOsub : interior (closedBallParam φ '' {b : closedBall (0 : E3) 1 |
          ‖(b : E3)‖ ≤ ρ₂ * (1 + a)}) \
            closedBallParam φ '' {b : closedBall (0 : E3) 1 | ‖(b : E3)‖ ≤ ρ₂ * (1 - a)} ⊆
              range ρc := by
        rintro y ⟨hy1, hy2⟩
        rw [hIint] at hy1
        obtain ⟨b, hbhi, rfl⟩ := hy1
        have hblo : ρ₂ * (1 - a) < ‖(b : E3)‖ := by
          by_contra hle
          exact hy2 ⟨b, not_lt.mp hle, rfl⟩
        have hbhi' : ‖(b : E3)‖ < ρ₂ * (1 + a) := hbhi
        have hvpos : 0 < ‖(b : E3)‖ := lt_of_le_of_lt (by nlinarith) hblo
        have hm₀ : ρ₂ • ‖(b : E3)‖⁻¹ • (b : E3) ∈ closedBall (0 : E3) 1 := by
          rw [mem_closedBall_zero_iff, norm_smul, norm_smul, Real.norm_of_nonneg hρ₂0.le,
            Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le), inv_mul_cancel₀ hvpos.ne', mul_one]
          exact hρ₂1.le
        have hb₀ : ‖((⟨ρ₂ • ‖(b : E3)‖⁻¹ • (b : E3), hm₀⟩ : closedBall (0 : E3) 1) : E3)‖ =
            ρ₂ := by
          change ‖ρ₂ • ‖(b : E3)‖⁻¹ • (b : E3)‖ = ρ₂
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hρ₂0.le,
            Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le), inv_mul_cancel₀ hvpos.ne', mul_one]
        have hs : ‖(b : E3)‖ / ρ₂ - 1 ∈ Icc (-a) a := by
          constructor
          · rw [le_sub_iff_add_le, le_div_iff₀ hρ₂0]
            nlinarith
          · rw [sub_le_iff_le_add, div_le_iff₀ hρ₂0]
            nlinarith
        refine ⟨(⟨closedBallParam φ ⟨_, hm₀⟩, ⟨_, hm₀⟩, hb₀, rfl⟩, ⟨_, hs⟩), ?_⟩
        change closedBallParam φ ⟨(1 + (‖(b : E3)‖ / ρ₂ - 1)) • _, _⟩ = closedBallParam φ b
        congr 1
        apply Subtype.ext
        change (1 + (‖(b : E3)‖ / ρ₂ - 1)) •
          ((φ ⟨closedBallParam φ ⟨_, hm₀⟩, _⟩ : closedBall (0 : E3) 1) : E3) = b
        rw [show (φ ⟨closedBallParam φ ⟨_, hm₀⟩, hF₂Y _ ⟨⟨_, hm₀⟩, hb₀, rfl⟩⟩ :
          closedBall (0 : E3) 1) = ⟨_, hm₀⟩ from hφg ⟨_, hm₀⟩]
        change (1 + (‖(b : E3)‖ / ρ₂ - 1)) • (ρ₂ • ‖(b : E3)‖⁻¹ • (b : E3)) = b
        rw [smul_smul, smul_smul]
        have hcoef : (1 + (‖(b : E3)‖ / ρ₂ - 1)) * ρ₂ * ‖(b : E3)‖⁻¹ = 1 := by
          field_simp
          ring
        rw [hcoef, one_smul]
      obtain ⟨b, hb, rfl⟩ := hx
      have hb' : ‖(b : E3)‖ = ρ₂ := hb
      have hxO : closedBallParam φ b ∈ interior (closedBallParam φ '' {b : closedBall (0 : E3) 1 |
          ‖(b : E3)‖ ≤ ρ₂ * (1 + a)}) \
            closedBallParam φ '' {b : closedBall (0 : E3) 1 | ‖(b : E3)‖ ≤ ρ₂ * (1 - a)} := by
        refine ⟨?_, ?_⟩
        · rw [hIint]
          refine ⟨b, ?_, rfl⟩
          change ‖(b : E3)‖ < ρ₂ * (1 + a)
          rw [hb']
          nlinarith
        · rintro ⟨b', hb'', hbb'⟩
          rw [hgi hbb'] at hb''
          have hle : ‖(b : E3)‖ ≤ ρ₂ * (1 - a) := hb''
          rw [hb'] at hle
          nlinarith
      exact Filter.mem_of_superset (hO.mem_nhds hxO) hOsub
    obtain ⟨c, -⟩ := exists_twoSidedCollar_of_closedInterval ha0 ρc
      (hρcc.isClosedEmbedding hρci).isEmbedding hzero hnbhd
    exact ⟨c⟩

theorem Moise305Tame.exists_isPLBall_of_isTopologicalCell {Y K : Set E3}
    (hY : IsTopologicalCell 3 Y) (hK : IsCompact K) (hKY : K ⊆ interior Y) :
    ∃ C, IsPLBall 3 C ∧ K ⊆ interior C ∧ C ⊆ interior Y := by
  obtain ⟨C₁, C₂, h₁, h₂, hK₁, h₁₂, h₂Y, hshell, hbi⟩ :=
    hY.exists_nested_isSphericalShell_isBicollared hK hKY
  obtain ⟨C, hC, hC₁, hC₂⟩ := moise305Tame C₁ C₂ h₁ h₂ h₁₂ hshell hbi
  exact ⟨C, hC, hK₁.trans (interior_subset.trans hC₁), hC₂.trans (interior_subset.trans h₂Y)⟩

theorem Moise305Tame.exists_isPLCellOn_of_isTopologicalCell
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M) {Y K : Set M}
    (hYc : Y ⊆ c.source) (hY : IsTopologicalCell 3 (c '' Y)) (hK : IsCompact K)
    (hKY : K ⊆ interior Y) : ∃ C B : Set M, IsPLCellOn 3 C B ∧ K ⊆ interior C ∧ C ⊆ interior Y := by
  have hKs : K ⊆ c.source := hKY.trans (interior_subset.trans hYc)
  have hcK : IsCompact (c '' K) := hK.image_of_continuousOn (c.continuousOn.mono hKs)
  have hopen : IsOpen (c '' interior Y) :=
    c.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hYc)
  have hcKY : c '' K ⊆ interior (c '' Y) :=
    (image_mono hKY).trans (interior_maximal (image_mono interior_subset) hopen)
  obtain ⟨C₁, C₂, h₁, h₂, hK₁, h₁₂, h₂Y, hshell, hbi⟩ :=
    hY.exists_nested_isSphericalShell_isBicollared hcK hcKY
  have hYt : c '' Y ⊆ c.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_source (hYc hy)
  have h₂t : C₂ ⊆ c.target := (h₂Y.trans interior_subset).trans hYt
  have h₁t : C₁ ⊆ c.target := (h₁₂.trans interior_subset).trans h₂t
  have himg : ∀ {C' : Set E3}, C' ⊆ c.target → c '' (c.symm '' C') = C' :=
    fun h => c.image_symm_image_of_subset_target h
  have hsymmopen : ∀ {V : Set E3}, IsOpen V → V ⊆ c.target → IsOpen (c.symm '' V) :=
    fun hV hVt => c.isOpen_image_symm_of_subset_target hV hVt
  have hC₂s : c.symm '' C₂ ⊆ c.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_target (h₂t hy)
  have h₁₂' : c.symm '' C₁ ⊆ interior (c.symm '' C₂) :=
    (image_mono h₁₂).trans (interior_maximal (image_mono interior_subset)
      (hsymmopen isOpen_interior (interior_subset.trans h₂t)))
  obtain ⟨C, B, hCB, hC₁, hC₂⟩ := Moise305Tame.exists_isPLCellOn_of_mem_maximalAtlas hc hC₂s
    (by rw [himg h₁t]; exact h₁) (by rw [himg h₂t]; exact h₂) h₁₂'
    (by rw [himg h₁t, himg h₂t]; exact hshell) (by rw [himg h₂t]; exact hbi)
  refine ⟨C, B, hCB, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ c.source := hKs hx
    have hcx : c x ∈ interior C₁ := hK₁ ⟨x, hx, rfl⟩
    have hxint : x ∈ interior (c.symm '' C₁) := by
      refine interior_maximal (image_mono interior_subset)
        (hsymmopen isOpen_interior (interior_subset.trans h₁t)) ⟨c x, hcx, c.left_inv hxs⟩
    exact hC₁ (interior_subset hxint)
  · refine hC₂.trans (interior_subset.trans ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hyint : y ∈ interior (c '' Y) := h₂Y hy
    have hsub : c.symm '' interior (c '' Y) ⊆ interior Y := by
      refine interior_maximal ?_ (hsymmopen isOpen_interior (interior_subset.trans hYt))
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := interior_subset hz
      rw [c.left_inv (hYc hw)]
      exact hw
    exact hsub ⟨y, hyint, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
