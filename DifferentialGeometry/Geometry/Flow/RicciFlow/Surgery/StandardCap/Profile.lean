import DifferentialGeometry.Analysis.Calculus.Cutoff.SymmetricCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Set
open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

noncomputable def transitionStart : ℝ := Real.pi / Real.sqrt 2 - 1 / 2

noncomputable def transitionEnd : ℝ := transitionStart + 1

noncomputable def angle (r : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * ∫ t in (0 : ℝ)..r, Real.smoothTransition (transitionEnd - t)

noncomputable def warpingFunction (r : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (angle r)

theorem transitionStart_pos : 0 < transitionStart := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold transitionStart
  rw [sub_pos, lt_div_iff₀ hs]
  linarith [Real.two_le_pi]

theorem transitionStart_lt_transitionEnd : transitionStart < transitionEnd := by
  simp [transitionEnd]

theorem transitionEnd_pos : 0 < transitionEnd :=
  transitionStart_pos.trans transitionStart_lt_transitionEnd

private theorem continuous_transition :
    Continuous (fun t : ℝ => Real.smoothTransition (transitionEnd - t)) :=
  Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id)

theorem hasDerivAt_angle (r : ℝ) :
    HasDerivAt angle ((1 / Real.sqrt 2) * Real.smoothTransition (transitionEnd - r)) r := by
  exact (intervalIntegral.integral_hasDerivAt_right
    (continuous_transition.intervalIntegrable 0 r)
    continuous_transition.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_transition.continuousAt).const_mul _

theorem deriv_angle (r : ℝ) :
    deriv angle r = (1 / Real.sqrt 2) * Real.smoothTransition (transitionEnd - r) :=
  (hasDerivAt_angle r).deriv

theorem contDiff_angle : ContDiff ℝ ∞ angle := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun r => (hasDerivAt_angle r).differentiableAt
  · have heq : deriv angle = fun r =>
        (1 / Real.sqrt 2) * Real.smoothTransition (transitionEnd - r) := funext deriv_angle
    rw [heq]
    exact contDiff_const.mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem angle_eq_div_sqrt_two {r : ℝ} (hr : r ≤ transitionStart) :
    angle r = r / Real.sqrt 2 := by
  have hint : (∫ t in (0 : ℝ)..r, Real.smoothTransition (transitionEnd - t)) = r := by
    calc
      _ = ∫ _ in (0 : ℝ)..r, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply Real.smoothTransition.one_of_one_le
        have ht' : t ≤ max 0 r := ht.2
        have : max 0 r ≤ transitionStart := max_le transitionStart_pos.le hr
        dsimp [transitionEnd]
        linarith
      _ = r := by simp
  simp only [angle, hint]
  ring

@[simp] theorem angle_zero : angle 0 = 0 := by simp [angle]

private theorem integral_transitionStart_transitionEnd :
    (∫ t in transitionStart..transitionEnd,
      Real.smoothTransition (transitionEnd - t)) = 1 / 2 := by
  rw [intervalIntegral.integral_comp_sub_left]
  simp only [sub_self, transitionEnd, add_sub_cancel_left]
  exact DifferentialGeometry.Analysis.integral_smoothTransition

theorem angle_transitionEnd : angle transitionEnd = Real.pi / 2 := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (continuous_transition.intervalIntegrable (μ := MeasureTheory.volume) 0 transitionStart)
    (continuous_transition.intervalIntegrable (μ := MeasureTheory.volume) transitionStart transitionEnd)
  have htip := angle_eq_div_sqrt_two (r := transitionStart) le_rfl
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [integral_transitionStart_transitionEnd] at hsplit
  unfold angle at htip ⊢
  rw [← hsplit]
  rw [mul_add, htip]
  unfold transitionStart
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

theorem angle_eq_pi_div_two {r : ℝ} (hr : transitionEnd ≤ r) :
    angle r = Real.pi / 2 := by
  have hint : (∫ t in transitionEnd..r,
      Real.smoothTransition (transitionEnd - t)) = 0 := by
    calc
      _ = ∫ _ in transitionEnd..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply Real.smoothTransition.zero_of_nonpos
        have := (uIcc_of_le hr ▸ ht).1
        linarith
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (continuous_transition.intervalIntegrable (μ := MeasureTheory.volume) 0 transitionEnd)
    (continuous_transition.intervalIntegrable (μ := MeasureTheory.volume) transitionEnd r)
  rw [hint, add_zero] at hsplit
  unfold angle
  rw [← hsplit]
  exact angle_transitionEnd

theorem deriv_angle_nonneg (r : ℝ) : 0 ≤ deriv angle r := by
  rw [deriv_angle]
  exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)

theorem deriv_angle_le (r : ℝ) : deriv angle r ≤ 1 / Real.sqrt 2 := by
  rw [deriv_angle]
  exact mul_le_of_le_one_right (by positivity) (Real.smoothTransition.le_one _)

theorem monotone_angle : Monotone angle :=
  monotone_of_deriv_nonneg (fun r => (hasDerivAt_angle r).differentiableAt) deriv_angle_nonneg

theorem antitone_deriv_angle : Antitone (deriv angle) := by
  intro x y hxy
  simp only [deriv_angle]
  exact mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith)) (by positivity)

theorem deriv_deriv_angle_nonpos (r : ℝ) : deriv (deriv angle) r ≤ 0 :=
  antitone_deriv_angle.deriv_nonpos

theorem angle_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ angle r := by
  simpa using monotone_angle hr

theorem angle_le_pi_div_two (r : ℝ) : angle r ≤ Real.pi / 2 := by
  rcases le_total r transitionEnd with hr | hr
  · simpa only [angle_transitionEnd] using monotone_angle hr
  · exact (angle_eq_pi_div_two hr).le

theorem angle_pos {r : ℝ} (hr : 0 < r) : 0 < angle r := by
  rcases le_total r transitionStart with h | h
  · rw [angle_eq_div_sqrt_two h]
    positivity
  · have ha : 0 < angle transitionStart := by
      rw [angle_eq_div_sqrt_two le_rfl]
      exact div_pos transitionStart_pos (by positivity)
    exact ha.trans_le (monotone_angle h)

theorem angle_le_div_sqrt_two {r : ℝ} (hr : 0 ≤ r) :
    angle r ≤ r / Real.sqrt 2 := by
  have h := intervalIntegral.integral_mono_on hr
    (continuous_transition.intervalIntegrable (μ := MeasureTheory.volume) 0 r)
    (intervalIntegrable_const (c := (1 : ℝ)))
    (fun t _ => Real.smoothTransition.le_one (transitionEnd - t))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h
  unfold angle
  calc
    _ ≤ (1 / Real.sqrt 2) * r := mul_le_mul_of_nonneg_left h (by positivity)
    _ = r / Real.sqrt 2 := by ring

theorem contDiff_warpingFunction : ContDiff ℝ ∞ warpingFunction :=
  contDiff_const.mul contDiff_angle.sin

@[simp] theorem warpingFunction_zero : warpingFunction 0 = 0 := by
  simp [warpingFunction]

theorem warpingFunction_eq_sqrt_two_mul_sin {r : ℝ} (hr : r ≤ transitionStart) :
    warpingFunction r = Real.sqrt 2 * Real.sin (r / Real.sqrt 2) := by
  rw [warpingFunction, angle_eq_div_sqrt_two hr]

theorem warpingFunction_eq_sqrt_two {r : ℝ} (hr : transitionEnd ≤ r) :
    warpingFunction r = Real.sqrt 2 := by
  rw [warpingFunction, angle_eq_pi_div_two hr, Real.sin_pi_div_two, mul_one]

theorem warpingFunction_pos {r : ℝ} (hr : 0 < r) : 0 < warpingFunction r := by
  apply mul_pos (by positivity)
  exact Real.sin_pos_of_pos_of_lt_pi (angle_pos hr)
    ((angle_le_pi_div_two r).trans_lt (half_lt_self Real.pi_pos))

theorem warpingFunction_le_sqrt_two (r : ℝ) : warpingFunction r ≤ Real.sqrt 2 := by
  exact mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)

theorem warpingFunction_le {r : ℝ} (hr : 0 ≤ r) : warpingFunction r ≤ r := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  calc
    _ ≤ Real.sqrt 2 * angle r :=
      mul_le_mul_of_nonneg_left (Real.sin_le (angle_nonneg hr)) (by positivity)
    _ ≤ Real.sqrt 2 * (r / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left (angle_le_div_sqrt_two hr) (by positivity)
    _ = r := by field_simp

theorem hasDerivAt_warpingFunction (r : ℝ) :
    HasDerivAt warpingFunction
      (Real.sqrt 2 * Real.cos (angle r) * deriv angle r) r := by
  have ha := (contDiff_angle.differentiable (by simp) r).hasDerivAt
  change HasDerivAt (fun y => Real.sqrt 2 * Real.sin (angle y))
    (Real.sqrt 2 * Real.cos (angle r) * deriv angle r) r
  simpa only [mul_assoc] using ha.sin.const_mul (Real.sqrt 2)

theorem deriv_warpingFunction (r : ℝ) :
    deriv warpingFunction r = Real.sqrt 2 * Real.cos (angle r) * deriv angle r :=
  (hasDerivAt_warpingFunction r).deriv

theorem deriv_deriv_warpingFunction (r : ℝ) :
    deriv (deriv warpingFunction) r = Real.sqrt 2 *
      (Real.cos (angle r) * deriv (deriv angle) r -
        Real.sin (angle r) * (deriv angle r) ^ 2) := by
  have ha := (contDiff_angle.differentiable (by simp) r).hasDerivAt
  have had := ((contDiff_infty_iff_deriv.mp contDiff_angle).2.differentiable (by simp) r).hasDerivAt
  have h := ((ha.cos.const_mul (Real.sqrt 2)).mul had).deriv
  have heq : deriv warpingFunction = fun r =>
      Real.sqrt 2 * Real.cos (angle r) * deriv angle r := funext deriv_warpingFunction
  rw [heq]
  change deriv ((fun y => Real.sqrt 2 * Real.cos (angle y)) * deriv angle) r = _
  rw [h]
  ring

theorem deriv_warpingFunction_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ deriv warpingFunction r := by
  rw [deriv_warpingFunction]
  exact mul_nonneg (mul_nonneg (by positivity)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg hr, Real.pi_pos],
      angle_le_pi_div_two r⟩)) (deriv_angle_nonneg r)

theorem deriv_warpingFunction_le_one (r : ℝ) : deriv warpingFunction r ≤ 1 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [deriv_warpingFunction]
  calc
    _ ≤ Real.sqrt 2 * 1 * deriv angle r :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.cos_le_one _) (by positivity))
        (deriv_angle_nonneg r)
    _ ≤ Real.sqrt 2 * 1 * (1 / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left (deriv_angle_le r) (by positivity)
    _ = 1 := by field_simp

theorem deriv_deriv_warpingFunction_nonpos {r : ℝ} (hr : 0 ≤ r) :
    deriv (deriv warpingFunction) r ≤ 0 := by
  rw [deriv_deriv_warpingFunction]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply sub_nonpos.mpr
  calc
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg hr, Real.pi_pos],
        angle_le_pi_div_two r⟩) (deriv_deriv_angle_nonpos r)
    _ ≤ _ := mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨angle_nonneg hr,
        (angle_le_pi_div_two r).trans (half_le_self Real.pi_pos.le)⟩) (sq_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
