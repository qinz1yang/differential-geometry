import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem iteratedDeriv_eq_zero_of_eqOn_Ici
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a : ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : EqOn f (fun _ => 0) (Ici a)) (n : ℕ) :
    iteratedDeriv n f a = 0 := by
  have heq : EqOn f (fun _ => 0) (Ioi a) := fun _ hx => hzero (Ioi_subset_Ici_self hx)
  have hd : EqOn (iteratedDeriv n f) (fun _ => 0) (Ioi a) := by
    intro x hx
    simpa only [iteratedDeriv_fun_const_zero] using
      heq.iteratedDeriv_of_isOpen isOpen_Ioi n hx
  have hc := hd.closure (hf.continuous_iteratedDeriv n
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) continuous_const
  exact hc (by simp only [closure_Ioi, mem_Ici, le_refl])

theorem abs_log_cos_le_sq {β : ℝ} (hcos : 1 / 2 ≤ Real.cos β) :
    |Real.log (Real.cos β)| ≤ β ^ 2 := by
  have hc : 0 < Real.cos β := lt_of_lt_of_le (by norm_num) hcos
  rw [abs_of_nonpos (Real.log_nonpos hc.le (Real.cos_le_one β))]
  calc
    -Real.log (Real.cos β) ≤ (1 - Real.cos β) / Real.cos β := by
      have hl := Real.one_sub_inv_le_log_of_pos hc
      rw [sub_div, div_self hc.ne', one_div]
      linarith
    _ ≤ β ^ 2 := by
      apply (div_le_iff₀ hc).mpr
      have hmul := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hcos)
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := β)]

theorem relative_log_cos_bounds {β speed accel s : ℝ}
    (hβ : β ∈ Icc 0 (Real.pi / 2)) (hspeed : 0 < speed) (haccel : 0 ≤ accel)
    (hcos : 1 / 2 ≤ Real.cos β) (hwidth : β ≤ s * speed) :
    let D := Real.cos β * (accel * Real.sin β + speed ^ 2 * Real.cos β)
    0 < D ∧ |Real.log (Real.cos β)| ≤ 4 * s ^ 2 * D ∧
      speed * Real.sin β ≤ 4 * s * D := by
  let D := Real.cos β * (accel * Real.sin β + speed ^ 2 * Real.cos β)
  have hsin : 0 ≤ Real.sin β := Real.sin_nonneg_of_mem_Icc
    ⟨hβ.1, hβ.2.trans (half_le_self Real.pi_pos.le)⟩
  have hc : 0 < Real.cos β := lt_of_lt_of_le (by norm_num) hcos
  have hs : 0 ≤ s := by nlinarith [hβ.1]
  have hquarter : speed ^ 2 / 4 ≤ D := by
    have hterm := mul_nonneg hc.le (mul_nonneg haccel hsin)
    have hsq : 1 / 4 ≤ (Real.cos β) ^ 2 := by nlinarith
    have hmul := mul_nonneg (sq_nonneg speed) (sub_nonneg.mpr hsq)
    dsimp only [D]
    nlinarith
  refine ⟨(div_pos (sq_pos_of_pos hspeed) (by norm_num)).trans_le hquarter, ?_, ?_⟩
  · have hβsq : β ^ 2 ≤ (s * speed) ^ 2 :=
      pow_le_pow_left₀ hβ.1 hwidth 2
    have hmul := mul_le_mul_of_nonneg_left hquarter (sq_nonneg s)
    exact (abs_log_cos_le_sq hcos).trans (by nlinarith)
  · have hfirst := mul_le_mul_of_nonneg_left (Real.sin_le hβ.1) hspeed.le
    have hsecond := mul_le_mul_of_nonneg_left hwidth hspeed.le
    have hthird := mul_le_mul_of_nonneg_left hquarter hs
    nlinarith

end DifferentialGeometry.Analysis
