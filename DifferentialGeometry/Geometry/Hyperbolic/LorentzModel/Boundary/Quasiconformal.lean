/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Distortion

noncomputable section

namespace DifferentialGeometry.BoundaryQuasiconformal

open HyperbolicBoundary BoundaryTopology BoundaryHomeomorph BoundaryVisual BoundaryDistortion

variable {n : ℕ}

def HasLocalMetricDistortion (φ : BoundaryH n → BoundaryH n) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ∀ a : BoundaryH n, ∃ U : Set (BoundaryH n),
    IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, ∀ c ∈ U, chordDist a b ≤ chordDist a c →
      chordDist (φ a) (φ b) ≤ H * chordDist (φ a) (φ c)

theorem exists_local_ratio_bound (φ : BoundaryH n ≃ₜ BoundaryH n)
    (hφ : HasCrossRatioControl φ) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : BoundaryH n, ∃ U : Set (BoundaryH n),
      IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, ∀ c ∈ U, bratioB a b ≤ bratioB a c →
        bratioB (φ a) (φ b) ≤ L * bratioB (φ a) (φ c) := by
  obtain ⟨D, α, β, hD, hα, hβ, hbound⟩ := hφ
  let M := distortion D α β 2
  have hM : 0 ≤ M := distortion_nonneg hD.le (by norm_num)
  let L := max 1 (4 * M)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨L, hL, fun a => ?_⟩
  let d := antipode a
  have had : a ≠ d := ne_antipode a
  let P := bratioB (φ a) (φ d)
  have hP : 0 < P := bratioB_pos (fun h => had (φ.injective h))
  have hs : Continuous (fun x : BoundaryH n => bratioB x d) := continuous_bratioB_right d
  have ht : Continuous (fun x : BoundaryH n => bratioB (φ x) (φ d)) :=
    (continuous_bratioB_right (φ d)).comp φ.continuous
  let U : Set (BoundaryH n) :=
    {x | 1 < bratioB x d ∧ P / 2 < bratioB (φ x) (φ d) ∧ bratioB (φ x) (φ d) < 2 * P}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hs).inter
      ((isOpen_lt continuous_const ht).inter (isOpen_lt ht continuous_const))
  have haU : a ∈ U := by
    change 1 < bratioB a (antipode a) ∧ P / 2 < P ∧ P < 2 * P
    rw [bratioB_self_antipode]
    exact ⟨by norm_num, by linarith, by linarith⟩
  refine ⟨U, hU, haU, fun b hb c hc hcomp => ?_⟩
  by_cases hab : a = b
  · subst b
    rw [bratioB_self]
    exact mul_nonneg hL.le (bratioB_nonneg _ _)
  by_cases hbc : b = c
  · subst c
    exact le_mul_of_one_le_left (bratioB_nonneg _ _) (le_max_left _ _)
  have hac : a ≠ c := by
    intro heq
    rw [← heq, bratioB_self] at hcomp
    exact (not_le_of_gt (bratioB_pos hab)) hcomp
  have hbd : b ≠ d := by
    intro heq
    have h := hb.1
    rw [heq, bratioB_self] at h
    norm_num at h
  have ht₂ : crossRatioSq a b c d ≤ 2 := by
    unfold crossRatioSq
    apply (div_le_iff₀ (mul_pos (bratioB_pos hac) (bratioB_pos hbd))).mpr
    have hnum : bratioB a b * bratioB c d ≤ 2 * bratioB a c := by
      have h := mul_le_mul hcomp (bratioB_le_two c d) (bratioB_nonneg c d) (bratioB_nonneg a c)
      linarith
    have hden : bratioB a c ≤ bratioB a c * bratioB b d :=
      le_mul_of_one_le_right (bratioB_nonneg a c) (le_of_lt hb.1)
    linarith
  have hcr : crossRatioSq (φ a) (φ b) (φ c) (φ d) ≤ M :=
    (hbound a b c d hab hac hbc hbd).trans
      ((strictMonoOn_distortion hD hα hβ).monotoneOn
        (crossRatioSq_nonneg a b c d) (by norm_num) ht₂)
  have hac' : 0 < bratioB (φ a) (φ c) := bratioB_pos (fun h => hac (φ.injective h))
  have hbd' : 0 < bratioB (φ b) (φ d) := bratioB_pos (fun h => hbd (φ.injective h))
  have hcd' : 0 < bratioB (φ c) (φ d) := lt_of_lt_of_le (by linarith : 0 < P / 2) hc.2.1.le
  have hrel : bratioB (φ b) (φ d) ≤ 4 * bratioB (φ c) (φ d) := by
    have h₁ := hb.2.2
    have h₂ := hc.2.1
    linarith
  have hnum : bratioB (φ a) (φ b) * bratioB (φ c) (φ d) ≤
      M * (bratioB (φ a) (φ c) * bratioB (φ b) (φ d)) :=
    (div_le_iff₀ (mul_pos hac' hbd')).mp hcr
  have htarget : bratioB (φ a) (φ b) ≤ (4 * M) * bratioB (φ a) (φ c) := by
    apply le_of_mul_le_mul_right ?_ hcd'
    calc bratioB (φ a) (φ b) * bratioB (φ c) (φ d)
        ≤ M * (bratioB (φ a) (φ c) * bratioB (φ b) (φ d)) := hnum
      _ = (M * bratioB (φ a) (φ c)) * bratioB (φ b) (φ d) := by ring
      _ ≤ (M * bratioB (φ a) (φ c)) * (4 * bratioB (φ c) (φ d)) :=
        mul_le_mul_of_nonneg_left hrel (mul_nonneg hM hac'.le)
      _ = ((4 * M) * bratioB (φ a) (φ c)) * bratioB (φ c) (φ d) := by ring
  exact htarget.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hac'.le)

theorem hasLocalMetricDistortion_of_crossRatioControl (φ : BoundaryH n ≃ₜ BoundaryH n)
    (hφ : HasCrossRatioControl φ) : HasLocalMetricDistortion φ := by
  obtain ⟨L, hL, hlocal⟩ := exists_local_ratio_bound φ hφ
  refine ⟨Real.sqrt L, Real.sqrt_pos.mpr hL, fun a => ?_⟩
  obtain ⟨U, hU, ha, hbound⟩ := hlocal a
  refine ⟨U, hU, ha, fun b hb c hc hdist => ?_⟩
  have hsource : bratioB a b ≤ bratioB a c := by
    have h := pow_le_pow_left₀ (chordDist_nonneg a b) hdist 2
    rw [chordDist_sq, chordDist_sq] at h
    linarith
  have htarget := hbound b hb c hc hsource
  have hsquare : chordDist (φ a) (φ b) ^ 2 ≤ (Real.sqrt L * chordDist (φ a) (φ c)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL.le, chordDist_sq, chordDist_sq]
    linarith
  exact (sq_le_sq₀ (chordDist_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg L)
    (chordDist_nonneg _ _))).mp hsquare

end DifferentialGeometry.BoundaryQuasiconformal
