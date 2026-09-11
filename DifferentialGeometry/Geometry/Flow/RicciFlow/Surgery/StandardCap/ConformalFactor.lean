import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalCoordinate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.TerminalProfile
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetGluing.FlatJoin

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

def conformalFactor (z : ℝ) : ℝ :=
  Real.log (warpingFunction (conformalRadius z) / Real.sqrt 2)

private theorem conformalRatio_pos (z : ℝ) :
    0 < warpingFunction (conformalRadius z) / Real.sqrt 2 :=
  div_pos (warpingFunction_pos (conformalRadius_pos z)) (Real.sqrt_pos.mpr (by norm_num))

theorem contDiff_conformalFactor : ContDiff ℝ ∞ conformalFactor :=
  ((contDiff_warpingFunction.comp contDiff_conformalRadius).div_const (Real.sqrt 2)).log
    (fun z => (conformalRatio_pos z).ne')

theorem exp_two_conformalFactor (z : ℝ) :
    Real.exp (2 * conformalFactor z) =
      (warpingFunction (conformalRadius z) / Real.sqrt 2) ^ 2 := by
  rw [conformalFactor, two_mul, Real.exp_add, Real.exp_log (conformalRatio_pos z)]
  ring

theorem conformalFactor_eq_zero_of_nonneg {z : ℝ} (hz : 0 ≤ z) : conformalFactor z = 0 := by
  rw [conformalFactor, conformalRadius_cylindrical hz,
    warpingFunction_eq_sqrt_two (by linarith)]
  simp only [div_self (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', Real.log_one]

@[simp] theorem conformalFactor_zero : conformalFactor 0 = 0 :=
  conformalFactor_eq_zero_of_nonneg le_rfl

theorem iteratedDeriv_conformalFactor_zero (n : ℕ) : iteratedDeriv n conformalFactor 0 = 0 :=
  DifferentialGeometry.Analysis.iteratedDeriv_eq_zero_of_eqOn_Ici contDiff_conformalFactor
    (fun _ hz => conformalFactor_eq_zero_of_nonneg hz) n

theorem hasDerivAt_conformalFactor (z : ℝ) :
    HasDerivAt conformalFactor (deriv warpingFunction (conformalRadius z) / Real.sqrt 2) z := by
  have ha := ((contDiff_warpingFunction.differentiable (by simp)) (conformalRadius z)).hasDerivAt
  have h := ((ha.comp z (hasDerivAt_conformalRadius z)).div_const (Real.sqrt 2)).log
    (conformalRatio_pos z).ne'
  simp only [Function.comp_apply] at h
  convert! h using 1
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have ha0 := (warpingFunction_pos (conformalRadius_pos z)).ne'
  field_simp

theorem deriv_conformalFactor (z : ℝ) :
    deriv conformalFactor z = deriv warpingFunction (conformalRadius z) / Real.sqrt 2 :=
  (hasDerivAt_conformalFactor z).deriv

theorem deriv_deriv_conformalFactor (z : ℝ) :
    deriv (deriv conformalFactor) z =
      warpingFunction (conformalRadius z) * deriv (deriv warpingFunction) (conformalRadius z) / 2 := by
  have heq : deriv conformalFactor =
      fun z => deriv warpingFunction (conformalRadius z) / Real.sqrt 2 := funext deriv_conformalFactor
  rw [heq]
  have hd := (contDiff_infty_iff_deriv.mp contDiff_warpingFunction).2
  have h := ((((hd.differentiable (by simp)) (conformalRadius z)).hasDerivAt.comp z
    (hasDerivAt_conformalRadius z)).div_const (Real.sqrt 2)).deriv
  simp only [Function.comp_apply] at h
  rw [h]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [hs2]

theorem conformalFactor_eq_terminalAngleDeficit (z : ℝ) :
    conformalFactor z = Real.log (Real.cos (terminalAngleDeficit (transitionEnd - conformalRadius z))) := by
  rw [conformalFactor, terminalAngleDeficit, sub_sub_cancel, Real.cos_pi_div_two_sub,
    warpingFunction]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  congr 1
  field_simp

theorem deriv_conformalFactor_eq_terminalAngleDeficit (z : ℝ) :
    deriv conformalFactor z =
      deriv terminalAngleDeficit (transitionEnd - conformalRadius z) *
        Real.sin (terminalAngleDeficit (transitionEnd - conformalRadius z)) := by
  rw [deriv_conformalFactor, deriv_terminalAngleDeficit, terminalAngleDeficit,
    sub_sub_cancel, Real.sin_pi_div_two_sub, deriv_warpingFunction]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp

theorem neg_deriv_deriv_conformalFactor_eq_terminalAngleDeficit (z : ℝ) :
    -deriv (deriv conformalFactor) z =
      Real.cos (terminalAngleDeficit (transitionEnd - conformalRadius z)) *
        (deriv (deriv terminalAngleDeficit) (transitionEnd - conformalRadius z) *
            Real.sin (terminalAngleDeficit (transitionEnd - conformalRadius z)) +
          deriv terminalAngleDeficit (transitionEnd - conformalRadius z) ^ 2 *
            Real.cos (terminalAngleDeficit (transitionEnd - conformalRadius z))) := by
  rw [deriv_deriv_conformalFactor, deriv_deriv_terminalAngleDeficit,
    deriv_terminalAngleDeficit, terminalAngleDeficit, sub_sub_cancel,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, warpingFunction,
    deriv_deriv_warpingFunction]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have halg (t a b c d : ℝ) (ht : t ^ 2 = 2) :
      -(t * a * (t * (b * c - a * d ^ 2)) / 2) = a * (-c * b + d ^ 2 * a) := by
    calc
      _ = -(t ^ 2) * (a * (b * c - a * d ^ 2)) / 2 := by ring
      _ = _ := by rw [ht]; ring
  exact halg _ _ _ _ _ hs

end DifferentialGeometry.PDE.RicciFlow.StandardCap
