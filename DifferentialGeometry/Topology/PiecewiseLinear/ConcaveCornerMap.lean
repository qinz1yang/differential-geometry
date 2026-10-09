/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Complex Set
open scoped Real ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def concaveCornerRot : ℂ := exp (-((π / 4 : ℝ) : ℂ) * I)

noncomputable def concaveCornerMap (z : ℂ) : ℂ := (concaveCornerRot * z) ^ (2 / 3 : ℂ)

noncomputable def concaveCornerInv (w : ℂ) : ℂ := concaveCornerRot⁻¹ * w ^ (3 / 2 : ℂ)

def concaveQuadrant : Set ℂ := {z | 0 ≤ z.re ∨ 0 ≤ z.im}

theorem exp_log_norm_add_arg (z : ℂ) (hz : z ≠ 0) (θ : ℝ) :
    exp ((Real.log ‖z‖ : ℂ) + ((arg z + θ : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) * z := by
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : exp ((Real.log ‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
    rw [← ofReal_exp, Real.exp_log hn]
  conv_rhs => rw [← norm_mul_exp_arg_mul_I z, ← h1]
  rw [← exp_add, ← exp_add]
  congr 1
  push_cast
  ring

theorem arg_ge_of_mem_concaveQuadrant {z : ℂ} (hz : z ∈ concaveQuadrant) :
    -(π / 2) ≤ arg z := by
  rcases hz with h | h
  · exact (abs_le.mp (abs_arg_le_pi_div_two_iff.mpr h)).1
  · have := arg_nonneg_iff.mpr h
    linarith [Real.pi_pos]

theorem concaveCornerRot_mul {z : ℂ} (hz : z ≠ 0) :
    concaveCornerRot * z = exp ((Real.log ‖z‖ : ℂ) + ((arg z - π / 4 : ℝ) : ℂ) * I) := by
  rw [sub_eq_add_neg, exp_log_norm_add_arg z hz]
  unfold concaveCornerRot
  push_cast
  ring_nf

theorem concaveCornerMap_eq {z : ℂ} (hz : z ∈ concaveQuadrant) (hz0 : z ≠ 0) :
    concaveCornerMap z = exp (((2 / 3 * Real.log ‖z‖ : ℝ) : ℂ) +
      ((2 / 3 * (arg z - π / 4) : ℝ) : ℂ) * I) := by
  have hge := arg_ge_of_mem_concaveQuadrant hz
  have hle := arg_le_pi z
  have hrot := concaveCornerRot_mul hz0
  have hne : concaveCornerRot * z ≠ 0 := by rw [hrot]; exact exp_ne_zero _
  have hlog : log (concaveCornerRot * z) =
      (Real.log ‖z‖ : ℂ) + ((arg z - π / 4 : ℝ) : ℂ) * I := by
    rw [hrot]
    apply log_exp
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith [Real.pi_pos]
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith [Real.pi_pos]
  unfold concaveCornerMap
  rw [cpow_def_of_ne_zero hne, hlog]
  congr 1
  push_cast
  ring

theorem concaveCornerMap_zero : concaveCornerMap 0 = 0 := by
  unfold concaveCornerMap
  rw [mul_zero, zero_cpow (by norm_num)]

theorem concaveCornerInv_zero : concaveCornerInv 0 = 0 := by
  unfold concaveCornerInv
  rw [zero_cpow (by norm_num), mul_zero]

theorem abs_arg_le_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) : |arg w| ≤ π / 2 :=
  abs_arg_le_pi_div_two_iff.mpr hw

theorem concaveCornerInv_eq {w : ℂ} (hw0 : w ≠ 0) :
    concaveCornerInv w = exp (((3 / 2 * Real.log ‖w‖ : ℝ) : ℂ) +
      ((3 / 2 * arg w + π / 4 : ℝ) : ℂ) * I) := by
  have hlog : log w = (Real.log ‖w‖ : ℂ) + (arg w : ℂ) * I := by
    apply Complex.ext <;> simp [log_re, log_im]
  unfold concaveCornerInv concaveCornerRot
  rw [cpow_def_of_ne_zero hw0, hlog, ← exp_neg, ← exp_add]
  congr 1
  push_cast
  ring

theorem concaveCornerMap_re_nonneg {z : ℂ} (hz : z ∈ concaveQuadrant) :
    0 ≤ (concaveCornerMap z).re := by
  by_cases hz0 : z = 0
  · rw [hz0, concaveCornerMap_zero, zero_re]
  rw [concaveCornerMap_eq hz hz0, exp_re]
  have hge := arg_ge_of_mem_concaveQuadrant hz
  have hle := arg_le_pi z
  apply mul_nonneg (Real.exp_pos _).le
  simp only [ofReal_re, ofReal_im, I_re, mul_zero, I_im, mul_one, add_zero, add_im, mul_im,
    zero_add]
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [Real.pi_pos]

theorem concaveCornerInv_mem {w : ℂ} (hw : 0 ≤ w.re) : concaveCornerInv w ∈ concaveQuadrant := by
  by_cases hw0 : w = 0
  · rw [hw0, concaveCornerInv_zero]
    exact Or.inl le_rfl
  have ha := abs_le.mp (abs_arg_le_of_re_nonneg hw)
  rw [concaveCornerInv_eq hw0]
  simp only [concaveQuadrant, mem_ofPred_eq, exp_re, exp_im, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
  by_cases hθ : 3 / 2 * arg w + π / 4 ≤ π / 2
  · left
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  · right
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [Real.pi_pos]

theorem concaveCornerInv_map {z : ℂ} (hz : z ∈ concaveQuadrant) :
    concaveCornerInv (concaveCornerMap z) = z := by
  by_cases hz0 : z = 0
  · rw [hz0, concaveCornerMap_zero, concaveCornerInv_zero]
  have hge := arg_ge_of_mem_concaveQuadrant hz
  have hle := arg_le_pi z
  set A : ℂ := ((2 / 3 * Real.log ‖z‖ : ℝ) : ℂ) + ((2 / 3 * (arg z - π / 4) : ℝ) : ℂ) * I
    with hA
  have hK : concaveCornerMap z = exp A := concaveCornerMap_eq hz hz0
  have hlog : log (exp A) = A := by
    apply log_exp
    · simp only [hA, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add]
      nlinarith [Real.pi_pos]
    · simp only [hA, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add]
      nlinarith [Real.pi_pos]
  have hpow : exp A ^ (3 / 2 : ℂ) = concaveCornerRot * z := by
    rw [cpow_def_of_ne_zero (exp_ne_zero A), hlog, concaveCornerRot_mul hz0]
    congr 1
    rw [hA]
    push_cast
    ring
  unfold concaveCornerInv
  rw [hK, hpow, ← mul_assoc, inv_mul_cancel₀ (by unfold concaveCornerRot; exact exp_ne_zero _),
    one_mul]

theorem concaveCornerMap_inv {w : ℂ} (hw : 0 ≤ w.re) :
    concaveCornerMap (concaveCornerInv w) = w := by
  by_cases hw0 : w = 0
  · rw [hw0, concaveCornerInv_zero, concaveCornerMap_zero]
  have ha := abs_le.mp (abs_arg_le_of_re_nonneg hw)
  set B : ℂ := ((3 / 2 * Real.log ‖w‖ : ℝ) : ℂ) + ((3 / 2 * arg w : ℝ) : ℂ) * I with hB
  have hrot : concaveCornerRot * concaveCornerInv w = exp B := by
    unfold concaveCornerInv
    rw [← mul_assoc, mul_inv_cancel₀ (by unfold concaveCornerRot; exact exp_ne_zero _), one_mul,
      cpow_def_of_ne_zero hw0]
    congr 1
    have hlog : log w = (Real.log ‖w‖ : ℂ) + (arg w : ℂ) * I := by
      apply Complex.ext <;> simp [log_re, log_im]
    rw [hlog, hB]
    push_cast
    ring
  have hlog : log (exp B) = B := by
    apply log_exp
    · simp only [hB, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add]
      nlinarith [Real.pi_pos]
    · simp only [hB, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add]
      nlinarith [Real.pi_pos]
  unfold concaveCornerMap
  rw [hrot, cpow_def_of_ne_zero (exp_ne_zero B), hlog]
  have hlogw : log w = (Real.log ‖w‖ : ℂ) + (arg w : ℂ) * I := by
    apply Complex.ext <;> simp [log_re, log_im]
  conv_rhs => rw [← exp_log hw0, hlogw]
  congr 1
  rw [hB]
  push_cast
  ring

theorem concaveCornerRot_mul_mem_slitPlane {z : ℂ} (hz : z ∈ concaveQuadrant) (hz0 : z ≠ 0) :
    concaveCornerRot * z ∈ slitPlane := by
  have hge := arg_ge_of_mem_concaveQuadrant hz
  have hle := arg_le_pi z
  rw [concaveCornerRot_mul hz0, mem_slitPlane_iff]
  simp only [exp_re, exp_im, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
    mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
  by_cases h : |arg z - π / 4| < π / 2
  · left
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp h))
  · right
    apply mul_ne_zero (Real.exp_pos _).ne'
    rcases le_or_gt 0 (arg z - π / 4) with h0 | h0
    · exact (Real.sin_pos_of_pos_of_lt_pi (by
        rw [abs_of_nonneg h0] at h
        linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne'
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt h0 (by linarith [Real.pi_pos])).ne

theorem mem_slitPlane_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) : w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases hw.lt_or_eq with h | h
  · exact Or.inl h
  · right
    intro him
    exact hw0 (Complex.ext h.symm him)

theorem continuousOn_concaveCornerMap : ContinuousOn concaveCornerMap concaveQuadrant := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hmul : ContinuousAt (fun x : ℂ => concaveCornerRot * x) z :=
    (continuous_const.mul continuous_id).continuousAt
  by_cases hz0 : z = 0
  · subst hz0
    have h := continuousAt_cpow_const_of_re_pos (z := concaveCornerRot * 0) (w := (2 / 3 : ℂ))
      (Or.inl (by simp)) (by norm_num)
    exact h.comp hmul
  · exact (continuousAt_cpow_const (concaveCornerRot_mul_mem_slitPlane hz hz0)).comp hmul

theorem continuousOn_concaveCornerInv : ContinuousOn concaveCornerInv {w | 0 ≤ w.re} := by
  intro w hw
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.mul
  by_cases hw0 : w = 0
  · subst hw0
    exact continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)
  · exact continuousAt_cpow_const (mem_slitPlane_of_re_nonneg hw hw0)

theorem contDiffAt_cpow_const_of_mem_slitPlane {a c : ℂ} (ha : a ∈ slitPlane) :
    ContDiffAt ℝ ∞ (fun x : ℂ => x ^ c) a := by
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  have h : ContDiffAt ℂ ∞ (fun x : ℂ => exp (log x * c)) a :=
    contDiff_exp.contDiffAt.comp a ((contDiffAt_log ha).mul contDiffAt_const)
  have heq : (fun x : ℂ => exp (log x * c)) =ᶠ[nhds a] (fun x : ℂ => x ^ c) := by
    filter_upwards [isOpen_ne.mem_nhds ha0] with x hx
    rw [cpow_def_of_ne_zero hx]
  exact (h.congr_of_eventuallyEq heq.symm).restrict_scalars ℝ

theorem contDiffAt_concaveCornerMap {z : ℂ} (hz : z ∈ concaveQuadrant) (hz0 : z ≠ 0) :
    ContDiffAt ℝ ∞ concaveCornerMap z :=
  (contDiffAt_cpow_const_of_mem_slitPlane (concaveCornerRot_mul_mem_slitPlane hz hz0)).comp z
    (contDiffAt_const.mul contDiffAt_id)

theorem contDiffAt_concaveCornerInv {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) :
    ContDiffAt ℝ ∞ concaveCornerInv w :=
  contDiffAt_const.mul (contDiffAt_cpow_const_of_mem_slitPlane (mem_slitPlane_of_re_nonneg hw hw0))

theorem norm_concaveCornerMap {z : ℂ} (hz : z ∈ concaveQuadrant) :
    ‖concaveCornerMap z‖ = ‖z‖ ^ (2 / 3 : ℝ) := by
  by_cases hz0 : z = 0
  · rw [hz0, concaveCornerMap_zero, norm_zero, Real.zero_rpow (by norm_num)]
  rw [concaveCornerMap_eq hz hz0, norm_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz0)]
  ring_nf

theorem concaveCornerMap_re_eq_zero_iff {z : ℂ} (hz : z ∈ concaveQuadrant) :
    (concaveCornerMap z).re = 0 ↔ (z.re = 0 ∧ z.im ≤ 0) ∨ (z.im = 0 ∧ z.re ≤ 0) := by
  by_cases hz0 : z = 0
  · rw [hz0, concaveCornerMap_zero]
    simp
  have hge := arg_ge_of_mem_concaveQuadrant hz
  have hle := arg_le_pi z
  rw [concaveCornerMap_eq hz hz0, exp_re]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  rw [mul_eq_zero, or_iff_right (Real.exp_pos _).ne']
  constructor
  · intro hcos
    have hnot : ¬ (-(π / 2) < 2 / 3 * (arg z - π / 4) ∧ 2 / 3 * (arg z - π / 4) < π / 2) :=
      fun h => (Real.cos_pos_of_mem_Ioo h).ne' hcos
    rcases le_or_gt (2 / 3 * (arg z - π / 4)) (-(π / 2)) with h1 | h1
    · left
      have harg : arg z = -(π / 2) := by linarith
      obtain ⟨h1, h2⟩ := arg_eq_neg_pi_div_two_iff.mp harg
      exact ⟨h1, h2.le⟩
    · have h2 : π / 2 ≤ 2 / 3 * (arg z - π / 4) := by
        by_contra h2
        exact hnot ⟨h1, lt_of_not_ge h2⟩
      right
      have harg : arg z = π := le_antisymm hle (by linarith)
      obtain ⟨h1, h2⟩ := arg_eq_pi_iff.mp harg
      exact ⟨h2, h1.le⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hlt : z.im < 0 := lt_of_le_of_ne h2 (fun h => hz0 (Complex.ext h1 h))
      have harg : arg z = -(π / 2) := arg_eq_neg_pi_div_two_iff.mpr ⟨h1, hlt⟩
      rw [harg]
      have : 2 / 3 * (-(π / 2) - π / 4) = -(π / 2) := by ring
      rw [this, Real.cos_neg, Real.cos_pi_div_two]
    · have hlt : z.re < 0 := lt_of_le_of_ne h2 (fun h => hz0 (Complex.ext h h1))
      have harg : arg z = π := arg_eq_pi_iff.mpr ⟨hlt, h1⟩
      rw [harg]
      have : 2 / 3 * (π - π / 4) = π / 2 := by ring
      rw [this, Real.cos_pi_div_two]

end DifferentialGeometry.Topology.PiecewiseLinear
