import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.TerminalProfile
import DifferentialGeometry.Analysis.Calculus.Asymptotics.FlatExponentialIntegral

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private theorem coefficient_tendsto :
    Tendsto terminalGermCoefficient (𝓝[>] 0)
      (𝓝 (Real.exp 1 / Real.sqrt 2)) := by
  have h := contDiffOn_terminalGermCoefficient.continuousOn.continuousAt
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  simpa only [terminalGermCoefficient_zero] using h.tendsto.mono_left nhdsWithin_le_nhds

private theorem coefficient_deriv_tendsto :
    Tendsto (deriv terminalGermCoefficient) (𝓝[>] 0)
      (𝓝 (deriv terminalGermCoefficient 0)) := by
  exact (contDiffOn_terminalGermCoefficient.continuousOn_deriv_of_isOpen
    isOpen_Iio (by simp)).continuousAt
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)) |>.tendsto.mono_left nhdsWithin_le_nhds

private theorem deficit_second_deriv_germ {s : ℝ} (hs : s < 1) :
    deriv (deriv terminalAngleDeficit) s =
      deriv terminalGermCoefficient s * expNegInvGlue s +
      terminalGermCoefficient s * (s⁻¹ ^ 2 * expNegInvGlue s) := by
  have heq : deriv terminalAngleDeficit =ᶠ[𝓝 s]
      (fun t => terminalGermCoefficient t * expNegInvGlue t) := by
    filter_upwards [eventually_lt_nhds hs] with t ht
    exact deriv_terminalAngleDeficit_eq_germ ht
  have hc := (contDiffOn_terminalGermCoefficient.contDiffAt
    (Iio_mem_nhds hs)).differentiableAt (by simp)
  have hg : HasDerivAt expNegInvGlue (s⁻¹ ^ 2 * expNegInvGlue s) s := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 s
  exact heq.deriv_eq.trans (hc.hasDerivAt.mul hg).deriv

theorem tendsto_terminalAngleDeficit_div_exp :
    Tendsto (fun s : ℝ => terminalAngleDeficit s /
      ((Real.exp 1 / Real.sqrt 2) * s ^ 2 * Real.exp (-1 / s)))
      (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousOn terminalGermCoefficient (Icc 0 (1 / 2)) :=
    contDiffOn_terminalGermCoefficient.continuousOn.mono (fun _ hs =>
      hs.2.trans_lt (by norm_num))
  have h := DifferentialGeometry.Analysis.tendsto_integral_mul_expNegInvGlue_div
    (b := 1) (δ := 1 / 2) (by norm_num) (by norm_num) hc
    (terminalGermCoefficient_pos 0).ne'
  simp only [div_one, terminalGermCoefficient_zero] at h
  apply h.congr'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with s hs
  rw [terminalAngleDeficit_eq_integral_germ hs]

theorem tendsto_deriv_terminalAngleDeficit_div_exp :
    Tendsto (fun s : ℝ => deriv terminalAngleDeficit s /
      ((Real.exp 1 / Real.sqrt 2) * Real.exp (-1 / s)))
      (𝓝[>] 0) (𝓝 1) := by
  have hc0 : Real.exp 1 / Real.sqrt 2 ≠ 0 := by positivity
  have h := coefficient_tendsto.div_const (Real.exp 1 / Real.sqrt 2)
  simp only [div_self hc0] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with s hs hs1
  rw [deriv_terminalAngleDeficit_eq_exp hs hs1]
  field_simp

theorem tendsto_deriv_deriv_terminalAngleDeficit_div_exp :
    Tendsto (fun s : ℝ => deriv (deriv terminalAngleDeficit) s /
      ((Real.exp 1 / Real.sqrt 2) * s⁻¹ ^ 2 * Real.exp (-1 / s)))
      (𝓝[>] 0) (𝓝 1) := by
  have hc0 : Real.exp 1 / Real.sqrt 2 ≠ 0 := by positivity
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := ((hid.pow 2).mul coefficient_deriv_tendsto).add coefficient_tendsto
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_add] at h
  have hq := h.div_const (Real.exp 1 / Real.sqrt 2)
  simp only [div_self hc0] at hq
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with s hs hs1
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [deficit_second_deriv_germ hs1]
  have hg : expNegInvGlue s = Real.exp (-1 / s) := by
    simpa only [div_one] using DifferentialGeometry.Analysis.expNegInvGlue_div_eq_exp
      (b := 1) (by norm_num) hs
  rw [hg]
  field_simp

end DifferentialGeometry.PDE.RicciFlow.StandardCap
