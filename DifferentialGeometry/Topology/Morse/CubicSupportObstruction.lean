/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.CriticalPoint
import DifferentialGeometry.Topology.Morse.NormalForm.Local
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! A boundary-value obstruction to cubic critical-pair cancellation in small neighborhoods. -/

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

private theorem cubic_suspension_sphere_lower_bound {x : MorseModel 2}
    (hx : x ∈ Metric.sphere 0 (3 / 2)) :
    -(3 / 8 : ℝ) ≤ x 0 ^ 3 / 3 - x 0 + x 1 ^ 2 := by
  have hn : ‖x‖ = (3 / 2 : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hx₀ : |x 0| ≤ (3 / 2 : ℝ) := (norm_le_pi_norm x 0).trans hn.le
  have hx₁ : |x 1| ≤ (3 / 2 : ℝ) := (norm_le_pi_norm x 1).trans hn.le
  have hside : |x 0| = (3 / 2 : ℝ) ∨ |x 1| = (3 / 2 : ℝ) := by
    by_contra hh
    push Not at hh
    have hlt : ‖x‖ < (3 / 2 : ℝ) := by
      apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
      intro i
      fin_cases i
      · exact hx₀.lt_of_ne hh.1
      · exact hx₁.lt_of_ne hh.2
    exact hn.not_lt hlt
  rcases hside with hside | hside
  · rcases le_total 0 (x 0) with hp | hn
    · rw [abs_of_nonneg hp] at hside
      rw [hside]
      nlinarith [sq_nonneg (x 1)]
    · rw [abs_of_nonpos hn] at hside
      have he : x 0 = -(3 / 2 : ℝ) := by linarith
      rw [he]
      nlinarith [sq_nonneg (x 1)]
  · have hy : x 1 ^ 2 = (3 / 2 : ℝ) ^ 2 := by
      rcases le_total 0 (x 1) with hp | hn
      · rw [abs_of_nonneg hp] at hside
        rw [hside]
      · rw [abs_of_nonpos hn] at hside
        nlinarith
    have hxlower := (abs_le.mp hx₀).1
    have hproduct : 0 ≤ (x 0 - 1) ^ 2 * (x 0 + 2) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith

theorem exists_isLocalMin_of_eqOn_cubic_compl_ball {r : ℝ}
    (hr : 1 ≤ r) (hr' : r < 3 / 2) {g : MorseModel 2 → ℝ} (hg : Continuous g)
    (heq : EqOn g (fun x => x 0 ^ 3 / 3 - x 0 + x 1 ^ 2)
      (Metric.ball (0 : MorseModel 2) r)ᶜ) :
    ∃ x ∈ Metric.ball (0 : MorseModel 2) (3 / 2), IsLocalMin g x := by
  let z : MorseModel 2 := ![r, 0]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hznorm : ‖z‖ = r := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hr0.le).mpr
      intro i
      fin_cases i
      · change |r| ≤ r
        simp only [abs_of_pos hr0, le_refl]
      · change ‖(0 : ℝ)‖ ≤ r
        simpa only [norm_zero] using hr0.le
    · have hh := norm_le_pi_norm z 0
      simpa only [z, Matrix.cons_val_zero, Real.norm_eq_abs, abs_of_pos hr0] using hh
  have hzout : z ∈ (Metric.ball (0 : MorseModel 2) r)ᶜ := by
    simp only [mem_compl_iff, Metric.mem_ball, dist_zero_right, hznorm, lt_self_iff_false,
      not_false_eq_true]
  have hz : z ∈ Metric.closedBall (0 : MorseModel 2) (3 / 2) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hznorm] using hr'.le
  have hzvalue : g z = r ^ 3 / 3 - r := by
    simpa only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      zero_pow (by decide : 2 ≠ 0), add_zero] using heq hzout
  have hzlt : g z < -(3 / 8 : ℝ) := by
    rw [hzvalue]
    have hproduct : 0 < (3 / 2 - r) * (r ^ 2 + 3 / 2 * r - 3 / 4) :=
      mul_pos (sub_pos.mpr hr') (by nlinarith [sq_nonneg (r - 1)])
    nlinarith
  apply Metric.exists_isLocalMin_mem_ball hg.continuousOn hz
  intro y hy
  have hynorm : ‖y‖ = (3 / 2 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hy
  have hyout : y ∈ (Metric.ball (0 : MorseModel 2) r)ᶜ := by
    simp only [mem_compl_iff, Metric.mem_ball, dist_zero_right, hynorm]
    exact not_lt.mpr hr'.le
  rw [heq hyout]
  exact hzlt.trans_le (cubic_suspension_sphere_lower_bound hy)

theorem not_exists_regular_cubic_perturbation_supported_in_ball {r : ℝ}
    (hr : 1 ≤ r) (hr' : r < 3 / 2) :
    ¬ ∃ g : MorseModel 2 → ℝ, ContDiff ℝ ∞ g ∧
      tsupport (fun x => g x - (x 0 ^ 3 / 3 - x 0 + x 1 ^ 2)) ⊆ Metric.ball 0 r ∧
      ∀ x, ¬ IsCriticalPointAt 𝓘(ℝ, MorseModel 2) g x := by
  rintro ⟨g, hg, hs, hregular⟩
  have heq : EqOn g (fun x => x 0 ^ 3 / 3 - x 0 + x 1 ^ 2)
      (Metric.ball (0 : MorseModel 2) r)ᶜ := by
    intro x hx
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun y => g y - (y 0 ^ 3 / 3 - y 0 + y 1 ^ 2)) (fun hh => hx (hs hh)))
  obtain ⟨x, _, hmin⟩ := exists_isLocalMin_of_eqOn_cubic_compl_ball hr hr' hg.continuous heq
  apply hregular x
  unfold IsCriticalPointAt
  rw [mfderiv_eq_fderiv]
  exact hmin.fderiv_eq_zero

end DifferentialGeometry.Morse
