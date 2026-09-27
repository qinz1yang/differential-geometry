import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Profile

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

def terminalAngleDeficit (s : ℝ) : ℝ := Real.pi / 2 - angle (transitionEnd - s)

theorem contDiff_terminalAngleDeficit : ContDiff ℝ ∞ terminalAngleDeficit :=
  contDiff_const.sub (contDiff_angle.comp (contDiff_const.sub contDiff_id))

@[simp] theorem terminalAngleDeficit_zero : terminalAngleDeficit 0 = 0 := by
  simp [terminalAngleDeficit, angle_transitionEnd]

theorem terminalAngleDeficit_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    terminalAngleDeficit s = 0 := by
  rw [terminalAngleDeficit, angle_eq_pi_div_two (by linarith), sub_self]

theorem hasDerivAt_terminalAngleDeficit (s : ℝ) :
    HasDerivAt terminalAngleDeficit (deriv angle (transitionEnd - s)) s := by
  have h := (((contDiff_angle.differentiable (by simp)) (transitionEnd - s)).hasDerivAt.comp s
    ((hasDerivAt_id s).const_sub transitionEnd)).const_sub (Real.pi / 2)
  convert! h using 1
  simp

theorem deriv_terminalAngleDeficit (s : ℝ) :
    deriv terminalAngleDeficit s = deriv angle (transitionEnd - s) :=
  (hasDerivAt_terminalAngleDeficit s).deriv

theorem deriv_deriv_terminalAngleDeficit (s : ℝ) :
    deriv (deriv terminalAngleDeficit) s = -deriv (deriv angle) (transitionEnd - s) := by
  have heq : deriv terminalAngleDeficit = fun t => deriv angle (transitionEnd - t) :=
    funext deriv_terminalAngleDeficit
  rw [heq]
  have hd := (contDiff_infty_iff_deriv.mp contDiff_angle).2
  convert! (((hd.differentiable (by simp)) (transitionEnd - s)).hasDerivAt.comp s
    ((hasDerivAt_id s).const_sub transitionEnd)).deriv using 1
  simp

theorem deriv_terminalAngleDeficit_pos {s : ℝ} (hs : 0 < s) :
    0 < deriv terminalAngleDeficit s := by
  rw [deriv_terminalAngleDeficit, deriv_angle]
  simp only [sub_sub_cancel]
  exact mul_pos (by positivity) (Real.smoothTransition.pos_of_pos hs)

@[simp] theorem deriv_terminalAngleDeficit_zero : deriv terminalAngleDeficit 0 = 0 := by
  rw [deriv_terminalAngleDeficit, deriv_angle]
  simp

theorem deriv_deriv_terminalAngleDeficit_nonneg (s : ℝ) :
    0 ≤ deriv (deriv terminalAngleDeficit) s := by
  rw [deriv_deriv_terminalAngleDeficit]
  exact neg_nonneg.mpr (deriv_deriv_angle_nonpos _)

theorem terminalAngleDeficit_nonneg (s : ℝ) : 0 ≤ terminalAngleDeficit s :=
  sub_nonneg.mpr (angle_le_pi_div_two _)

theorem terminalAngleDeficit_pos {s : ℝ} (hs : 0 < s) :
    0 < terminalAngleDeficit s := by
  have hmono : StrictMonoOn terminalAngleDeficit (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) contDiff_terminalAngleDeficit.continuous.continuousOn
      (fun t ht => deriv_terminalAngleDeficit_pos (by simpa only [interior_Ici, mem_Ioi] using ht))
  simpa only [terminalAngleDeficit_zero] using
    hmono (by simp only [mem_Ici, le_refl]) (show s ∈ Ici 0 from hs.le) hs

theorem terminalAngleDeficit_lt_pi_div_two {s : ℝ} (hs : s < transitionEnd) :
    terminalAngleDeficit s < Real.pi / 2 :=
  sub_lt_self _ (angle_pos (sub_pos.mpr hs))

private theorem integral_terminal_speed (s : ℝ) :
    (∫ t in (0 : ℝ)..s, deriv terminalAngleDeficit t) = terminalAngleDeficit s := by
  have hd := (contDiff_infty_iff_deriv.mp contDiff_terminalAngleDeficit).2
  have h := intervalIntegral.integral_deriv_eq_sub
    (fun t _ => (contDiff_terminalAngleDeficit.differentiable (by simp)) t)
    (hd.continuous.intervalIntegrable 0 s)
  simpa only [terminalAngleDeficit_zero, sub_zero] using h

theorem terminalAngleDeficit_le_mul_deriv {s : ℝ} (hs : 0 ≤ s) :
    terminalAngleDeficit s ≤ s * deriv terminalAngleDeficit s := by
  have hmono : Monotone (deriv terminalAngleDeficit) := by
    intro x y hxy
    simp only [deriv_terminalAngleDeficit]
    exact antitone_deriv_angle (by linarith)
  have hd := (contDiff_infty_iff_deriv.mp contDiff_terminalAngleDeficit).2
  have h := intervalIntegral.integral_mono_on hs
    (hd.continuous.intervalIntegrable (μ := MeasureTheory.volume) 0 s)
    (intervalIntegrable_const (c := deriv terminalAngleDeficit s))
    (fun t ht => hmono ht.2)
  simpa only [integral_terminal_speed, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] using h

theorem tendsto_terminalAngleDeficit_zero :
    Tendsto terminalAngleDeficit (𝓝 0) (𝓝 0) := by
  simpa only [terminalAngleDeficit_zero] using contDiff_terminalAngleDeficit.continuous.tendsto 0

def terminalGermCoefficient (s : ℝ) : ℝ :=
  1 / (Real.sqrt 2 * (Real.exp (-(1 - s)⁻¹) + expNegInvGlue s))

theorem terminalGermCoefficient_pos (s : ℝ) : 0 < terminalGermCoefficient s :=
  one_div_pos.mpr (mul_pos (by positivity)
    (add_pos_of_pos_of_nonneg (Real.exp_pos _) (expNegInvGlue.nonneg s)))

theorem contDiffOn_terminalGermCoefficient :
    ContDiffOn ℝ ∞ terminalGermCoefficient (Iio 1) := by
  intro s hs
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
  have he : ContDiffAt ℝ ∞ (fun t : ℝ => Real.exp (-(1 - t)⁻¹)) s :=
    (((contDiffAt_const.sub contDiffAt_id).inv hne).neg).exp
  have hden : Real.sqrt 2 * (Real.exp (-(1 - s)⁻¹) + expNegInvGlue s) ≠ 0 :=
    ne_of_gt (mul_pos (by positivity)
      (add_pos_of_pos_of_nonneg (Real.exp_pos _) (expNegInvGlue.nonneg s)))
  exact (contDiffAt_const.div (contDiffAt_const.mul
    (he.add expNegInvGlue.contDiff.contDiffAt)) hden).contDiffWithinAt

@[simp] theorem terminalGermCoefficient_zero :
    terminalGermCoefficient 0 = Real.exp 1 / Real.sqrt 2 := by
  simp [terminalGermCoefficient, Real.exp_neg, div_eq_mul_inv, mul_comm]

theorem deriv_terminalAngleDeficit_eq_germ {s : ℝ} (hs : s < 1) :
    deriv terminalAngleDeficit s = terminalGermCoefficient s * expNegInvGlue s := by
  have he : expNegInvGlue (1 - s) = Real.exp (-(1 - s)⁻¹) := by
    rw [expNegInvGlue, if_neg (not_le.mpr (sub_pos.mpr hs))]
  rw [deriv_terminalAngleDeficit, deriv_angle]
  simp only [sub_sub_cancel, Real.smoothTransition, he, terminalGermCoefficient]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

theorem deriv_terminalAngleDeficit_eq_exp {s : ℝ} (hs : 0 < s) (hsmall : s < 1) :
    deriv terminalAngleDeficit s = terminalGermCoefficient s * Real.exp (-1 / s) := by
  rw [deriv_terminalAngleDeficit_eq_germ hsmall, expNegInvGlue, if_neg hs.not_ge]
  simp only [neg_div, one_div]

theorem terminalAngleDeficit_eq_integral_germ {s : ℝ} (hs : s < 1) :
    terminalAngleDeficit s =
      ∫ t in (0 : ℝ)..s, terminalGermCoefficient t * expNegInvGlue t := by
  rw [← integral_terminal_speed s]
  apply intervalIntegral.integral_congr
  intro t ht
  exact deriv_terminalAngleDeficit_eq_germ (ht.2.trans_lt (max_lt zero_lt_one hs))

end DifferentialGeometry.PDE.RicciFlow.StandardCap
