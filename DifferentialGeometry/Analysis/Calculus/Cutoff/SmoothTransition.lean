import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

namespace Real.smoothTransition

theorem one_sub (x : ℝ) : smoothTransition (1 - x) = 1 - smoothTransition x := by
  unfold smoothTransition
  have hden := (pos_denom x).ne'
  rw [sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x))]
  field_simp
  ring

theorem integral_zero_one : (∫ x in (0 : ℝ)..1, smoothTransition x) = 1 / 2 := by
  have hcont : IntervalIntegrable smoothTransition MeasureTheory.volume 0 1 :=
    smoothTransition.continuous.intervalIntegrable 0 1
  have hchange :
      (∫ x in (0 : ℝ)..1, smoothTransition (1 - x)) =
        ∫ x in (0 : ℝ)..1, smoothTransition x := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (f := smoothTransition) (a := (0 : ℝ)) (b := 1) 1)
  simp_rw [one_sub] at hchange
  rw [intervalIntegral.integral_sub intervalIntegrable_const hcont] at hchange
  norm_num at hchange ⊢
  linarith

theorem integral_comp_sub_div (a b : ℝ) :
    (∫ x in a..b, smoothTransition ((x - a) / (b - a))) = (b - a) / 2 := by
  by_cases hab : b = a
  · subst b
    simp
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => smoothTransition (x / (b - a))) a]
    rw [intervalIntegral.integral_comp_div smoothTransition hba]
    simp only [sub_self, zero_div, div_self hba, integral_zero_one, smul_eq_mul]
    ring

open Set Filter
open scoped ContDiff Topology

theorem contDiff_one_sub_mul_sub (a b c : ℝ) :
    ContDiff ℝ ∞ (fun t => (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t)) :=
  (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a)))).mul
    (contDiff_const.sub contDiff_id)

theorem one_sub_mul_sub_eq_sub {a b c t : ℝ} (hab : a < b) (ht : t ≤ a) :
    (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t) = c - t := by
  rw [zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
    (sub_nonneg.mpr hab.le)), sub_zero, one_mul]

theorem one_sub_mul_sub_eq_zero {a b c t : ℝ} (hab : a < b) (ht : b ≤ t) :
    (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t) = 0 := by
  rw [one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), sub_self, zero_mul]

theorem one_sub_mul_sub_nonneg {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) (t : ℝ) :
    0 ≤ (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t) := by
  by_cases ht : b ≤ t
  · rw [one_sub_mul_sub_eq_zero hab ht]
  · exact mul_nonneg (sub_nonneg.mpr (le_one _))
      (sub_nonneg.mpr ((le_of_not_ge ht).trans hbc))

theorem antitone_one_sub_mul_sub {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) :
    Antitone (fun t => (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t)) := by
  intro x y hxy
  dsimp only
  by_cases hy : b ≤ y
  · rw [one_sub_mul_sub_eq_zero hab hy]
    exact one_sub_mul_sub_nonneg hab hbc x
  · have hχ := Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a)
        (sub_nonneg.mpr hab.le))
    exact mul_le_mul (sub_le_sub_left hχ 1) (sub_le_sub_left hxy c)
      (sub_nonneg.mpr ((le_of_not_ge hy).trans hbc)) (sub_nonneg.mpr (le_one _))

theorem strictAntiOn_one_sub_mul_sub {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) :
    StrictAntiOn (fun t => (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t))
      (Iio b) := by
  intro x _ y hy hxy
  dsimp only
  change y < b at hy
  have hχ := Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy.le a)
      (sub_nonneg.mpr hab.le))
  have hyχ : 0 < 1 - Real.smoothTransition ((y - a) / (b - a)) :=
    sub_pos.mpr (lt_one_of_lt_one ((div_lt_one (sub_pos.mpr hab)).mpr (by linarith)))
  exact (mul_lt_mul_of_pos_left (sub_lt_sub_left hxy c) hyχ).trans_le
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hχ 1)
      (sub_nonneg.mpr (hxy.le.trans (hy.le.trans hbc))))

theorem deriv_one_sub_mul_sub_nonpos {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) (t : ℝ) :
    deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t ≤ 0 :=
  (antitone_one_sub_mul_sub hab hbc).deriv_nonpos

theorem deriv_one_sub_mul_sub_neg {a b c t : ℝ} (hab : a < b) (hbc : b ≤ c) (ht : t < b) :
    deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t < 0 := by
  have hχ := (((show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff
    ).differentiable (by simp) _).hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const a).div_const (b - a))
  have hA := (hχ.const_sub 1).mul ((hasDerivAt_id t).const_sub c)
  have heq : deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t =
      -(deriv Real.smoothTransition ((t - a) / (b - a)) * (1 / (b - a))) * (c - t) +
        (1 - Real.smoothTransition ((t - a) / (b - a))) * (-1) := by
    simpa only [Function.comp_def, id_eq, Pi.mul_def] using hA.deriv
  rw [heq]
  have hd : 0 ≤ deriv Real.smoothTransition ((t - a) / (b - a)) * (1 / (b - a)) :=
    mul_nonneg Real.smoothTransition.monotone.deriv_nonneg (by positivity)
  have hct : 0 ≤ c - t := sub_nonneg.mpr (ht.le.trans hbc)
  have hχlt : Real.smoothTransition ((t - a) / (b - a)) < 1 :=
    lt_one_of_lt_one ((div_lt_one (sub_pos.mpr hab)).mpr (by linarith))
  nlinarith [mul_nonneg hd hct]

theorem deriv_one_sub_mul_sub_eq_neg_one {a b c t : ℝ} (hab : a < b) (ht : t < a) :
    deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t = -1 := by
  have hlocal : (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x))
      =ᶠ[𝓝 t] (fun x => c - x) := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact one_sub_mul_sub_eq_sub hab hx.le
  rw [hlocal.deriv_eq]
  exact ((hasDerivAt_id t).const_sub c).deriv


end Real.smoothTransition
