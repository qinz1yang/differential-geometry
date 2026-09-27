import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.TerminalAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private theorem deficit_tendsto :
    Tendsto terminalAngleDeficit (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_terminalAngleDeficit_zero.mono_left nhdsWithin_le_nhds

private theorem deficit_sin_div_tendsto :
    Tendsto (fun s : ℝ => Real.sin (terminalAngleDeficit s) / terminalAngleDeficit s)
      (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.continuous_sinc.tendsto 0).comp
    deficit_tendsto
  simp only [Function.comp_def, Real.sinc_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact Real.sinc_of_ne_zero (terminalAngleDeficit_pos hs).ne'

private theorem deficit_cos_tendsto :
    Tendsto (fun s : ℝ => Real.cos (terminalAngleDeficit s)) (𝓝[>] 0) (𝓝 1) := by
  simpa only [Function.comp_def, Real.cos_zero] using (Real.continuous_cos.tendsto 0).comp
    deficit_tendsto

private theorem deficit_cos_pos_lt_one {s : ℝ} (hs : 0 < s) (hL : s < transitionEnd) :
    0 < Real.cos (terminalAngleDeficit s) ∧ Real.cos (terminalAngleDeficit s) < 1 := by
  have hb := terminalAngleDeficit_pos hs
  have hbL := terminalAngleDeficit_lt_pi_div_two hL
  constructor
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hbL⟩
  · simpa only [Function.comp_def, Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl (0 : ℝ)) hbL.le hb

private theorem deficit_log_cos_div_sq_tendsto :
    Tendsto (fun s : ℝ => -Real.log (Real.cos (terminalAngleDeficit s)) /
      terminalAngleDeficit s ^ 2) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hcne : Tendsto (fun s : ℝ => Real.cos (terminalAngleDeficit s))
      (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨deficit_cos_tendsto, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds transitionEnd_pos)] with s hs hL
    exact (deficit_cos_pos_lt_one hs hL).2.ne
  have hl : Tendsto (fun s : ℝ => Real.log (Real.cos (terminalAngleDeficit s)) /
      (Real.cos (terminalAngleDeficit s) - 1)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, slope_def_field, Real.log_one, sub_zero, inv_one] using
      (Real.hasDerivAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto_slope.comp hcne
  have ht := (hl.mul (deficit_sin_div_tendsto.pow 2)).div
    (tendsto_const_nhds.add deficit_cos_tendsto) (by norm_num : (1 : ℝ) + 1 ≠ 0)
  norm_num only [one_mul, one_pow, one_add_one_eq_two] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds transitionEnd_pos)] with s hs hL
  have hb := (terminalAngleDeficit_pos hs).ne'
  have hc := deficit_cos_pos_lt_one hs hL
  have hc1 : Real.cos (terminalAngleDeficit s) - 1 ≠ 0 := sub_ne_zero.mpr hc.2.ne
  have hcp : 1 + Real.cos (terminalAngleDeficit s) ≠ 0 := (add_pos zero_lt_one hc.1).ne'
  have htrig := Real.sin_sq_add_cos_sq (terminalAngleDeficit s)
  dsimp only [Pi.div_apply]
  field_simp
  rw [show Real.sin (terminalAngleDeficit s) ^ 2 =
    1 - Real.cos (terminalAngleDeficit s) ^ 2 by linarith [htrig]]
  ring

private theorem exp_two_terminal (s : ℝ) :
    Real.exp (-2 / s) = Real.exp (-1 / s) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem tendsto_neg_conformalFactor_div_exp :
    Tendsto (fun s : ℝ => -conformalFactor (conformalCoordinate (transitionEnd - s)) /
      (s ^ 4 * Real.exp (-2 / s))) (𝓝[>] 0)
      (𝓝 ((Real.exp 1 / Real.sqrt 2) ^ 2 / 2)) := by
  have ht := (deficit_log_cos_div_sq_tendsto.mul
    (tendsto_terminalAngleDeficit_div_exp.pow 2)).mul_const
      ((Real.exp 1 / Real.sqrt 2) ^ 2)
  have hlim : (1 / 2 : ℝ) * 1 ^ 2 * (Real.exp 1 / Real.sqrt 2) ^ 2 =
      (Real.exp 1 / Real.sqrt 2) ^ 2 / 2 := by ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds transitionEnd_pos)] with s hs hL
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hb : terminalAngleDeficit s ≠ 0 := (terminalAngleDeficit_pos hs).ne'
  have hc0 : Real.exp 1 / Real.sqrt 2 ≠ 0 := by positivity
  rw [conformalFactor_eq_terminalAngleDeficit,
    conformalRadius_conformalCoordinate (sub_pos.mpr hL), sub_sub_cancel, exp_two_terminal]
  field_simp

theorem tendsto_deriv_conformalFactor_div_exp :
    Tendsto (fun s : ℝ => deriv conformalFactor (conformalCoordinate (transitionEnd - s)) /
      (s ^ 2 * Real.exp (-2 / s))) (𝓝[>] 0)
      (𝓝 ((Real.exp 1 / Real.sqrt 2) ^ 2)) := by
  have ht := ((tendsto_deriv_terminalAngleDeficit_div_exp.mul
    tendsto_terminalAngleDeficit_div_exp).mul deficit_sin_div_tendsto).mul_const
      ((Real.exp 1 / Real.sqrt 2) ^ 2)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds transitionEnd_pos)] with s hs hL
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hb : terminalAngleDeficit s ≠ 0 := (terminalAngleDeficit_pos hs).ne'
  have hc0 : Real.exp 1 / Real.sqrt 2 ≠ 0 := by positivity
  rw [deriv_conformalFactor_eq_terminalAngleDeficit,
    conformalRadius_conformalCoordinate (sub_pos.mpr hL), sub_sub_cancel, exp_two_terminal]
  field_simp

theorem tendsto_neg_deriv_deriv_conformalFactor_div_exp :
    Tendsto (fun s : ℝ => -deriv (deriv conformalFactor)
      (conformalCoordinate (transitionEnd - s)) / Real.exp (-2 / s)) (𝓝[>] 0)
      (𝓝 (2 * (Real.exp 1 / Real.sqrt 2) ^ 2)) := by
  have ht := deficit_cos_tendsto.mul
    ((((tendsto_deriv_deriv_terminalAngleDeficit_div_exp.mul
      tendsto_terminalAngleDeficit_div_exp).mul deficit_sin_div_tendsto).mul_const
        ((Real.exp 1 / Real.sqrt 2) ^ 2)).add
      (((tendsto_deriv_terminalAngleDeficit_div_exp.pow 2).mul deficit_cos_tendsto).mul_const
        ((Real.exp 1 / Real.sqrt 2) ^ 2)))
  have hlim : (1 : ℝ) * (1 * 1 * 1 * (Real.exp 1 / Real.sqrt 2) ^ 2 +
      1 ^ 2 * 1 * (Real.exp 1 / Real.sqrt 2) ^ 2) =
      2 * (Real.exp 1 / Real.sqrt 2) ^ 2 := by ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds transitionEnd_pos)] with s hs hL
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hb : terminalAngleDeficit s ≠ 0 := (terminalAngleDeficit_pos hs).ne'
  have hc0 : Real.exp 1 / Real.sqrt 2 ≠ 0 := by positivity
  rw [neg_deriv_deriv_conformalFactor_eq_terminalAngleDeficit,
    conformalRadius_conformalCoordinate (sub_pos.mpr hL), sub_sub_cancel, exp_two_terminal]
  field_simp

theorem tendsto_abs_conformalFactor_div_neg_deriv_deriv_div_pow :
    Tendsto (fun s : ℝ =>
      (|conformalFactor (conformalCoordinate (transitionEnd - s))| /
        (-deriv (deriv conformalFactor) (conformalCoordinate (transitionEnd - s)))) / s ^ 4)
      (𝓝[>] 0) (𝓝 (1 / 4 : ℝ)) := by
  have ht := tendsto_neg_conformalFactor_div_exp.div
    tendsto_neg_deriv_deriv_conformalFactor_div_exp
      (by positivity : 2 * (Real.exp 1 / Real.sqrt 2) ^ 2 ≠ 0)
  have hlim : ((Real.exp 1 / Real.sqrt 2) ^ 2 / 2) /
      (2 * (Real.exp 1 / Real.sqrt 2) ^ 2) = (1 / 4 : ℝ) := by
    field_simp
    norm_num
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds transitionEnd_pos)] with s hs hL
  have hF : conformalFactor (conformalCoordinate (transitionEnd - s)) < 0 := by
    rw [conformalFactor_eq_terminalAngleDeficit,
      conformalRadius_conformalCoordinate (sub_pos.mpr hL), sub_sub_cancel]
    exact Real.log_neg (deficit_cos_pos_lt_one hs hL).1 (deficit_cos_pos_lt_one hs hL).2
  dsimp only [Pi.div_apply]
  rw [div_div_div_comm, mul_div_cancel_right₀ _ (Real.exp_ne_zero _), abs_of_neg hF]

theorem tendsto_deriv_conformalFactor_div_neg_deriv_deriv_div_pow :
    Tendsto (fun s : ℝ =>
      (deriv conformalFactor (conformalCoordinate (transitionEnd - s)) /
        (-deriv (deriv conformalFactor) (conformalCoordinate (transitionEnd - s)))) / s ^ 2)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have ht := tendsto_deriv_conformalFactor_div_exp.div
    tendsto_neg_deriv_deriv_conformalFactor_div_exp
      (by positivity : 2 * (Real.exp 1 / Real.sqrt 2) ^ 2 ≠ 0)
  have hlim : ((Real.exp 1 / Real.sqrt 2) ^ 2) /
      (2 * (Real.exp 1 / Real.sqrt 2) ^ 2) = (1 / 2 : ℝ) := by
    field_simp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [] with s
  dsimp only [Pi.div_apply]
  rw [div_div_div_comm, mul_div_cancel_right₀ _ (Real.exp_ne_zero _)]

end DifferentialGeometry.PDE.RicciFlow.StandardCap
