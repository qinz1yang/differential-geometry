import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalFactor
import DifferentialGeometry.Analysis.Calculus.Derivative.DerivativeNorm

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Analysis

theorem conformalRadius_lt_transitionEnd {z : ℝ} (hz : z < 0) :
    conformalRadius z < transitionEnd := by
  simpa only [conformalRadius_zero] using strictMono_conformalRadius hz

theorem conformalFactor_signs_of_neg {z : ℝ} (hz : z < 0) :
    conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
      deriv (deriv conformalFactor) z < 0 := by
  let s := transitionEnd - conformalRadius z
  have hs : 0 < s := sub_pos.mpr (conformalRadius_lt_transitionEnd hz)
  have hβpos := terminalAngleDeficit_pos hs
  have hβlt : terminalAngleDeficit s < Real.pi / 2 :=
    terminalAngleDeficit_lt_pi_div_two (by dsimp [s]; linarith [conformalRadius_pos z])
  have hβpi : terminalAngleDeficit s < Real.pi := hβlt.trans (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (terminalAngleDeficit s) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβlt⟩
  have hcoslt : Real.cos (terminalAngleDeficit s) < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      ⟨le_rfl, Real.pi_pos.le⟩ ⟨hβpos.le, hβpi.le⟩ hβpos
  have hsin : 0 < Real.sin (terminalAngleDeficit s) :=
    Real.sin_pos_of_pos_of_lt_pi hβpos hβpi
  have hspeed := deriv_terminalAngleDeficit_pos hs
  refine ⟨?_, ?_, ?_⟩
  · rw [conformalFactor_eq_terminalAngleDeficit]
    exact Real.log_neg hcos hcoslt
  · rw [deriv_conformalFactor_eq_terminalAngleDeficit]
    exact mul_pos hspeed hsin
  · have hD := mul_pos hcos (add_pos_of_nonneg_of_pos
      (mul_nonneg (deriv_deriv_terminalAngleDeficit_nonneg s) hsin.le)
      (mul_pos (sq_pos_of_pos hspeed) hcos))
    rw [← neg_deriv_deriv_conformalFactor_eq_terminalAngleDeficit] at hD
    linarith

private theorem terminal_relative_bounds {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    let β := terminalAngleDeficit s
    let D := Real.cos β * (deriv (deriv terminalAngleDeficit) s * Real.sin β +
      (deriv terminalAngleDeficit s) ^ 2 * Real.cos β)
    0 < D ∧ |Real.log (Real.cos β)| ≤ 4 * s ^ 2 * D ∧
      deriv terminalAngleDeficit s * Real.sin β ≤ 4 * s * D := by
  have hone : 1 < transitionEnd := by
    dsimp only [transitionEnd]
    linarith [transitionStart_pos]
  have hβ : terminalAngleDeficit s ∈ Icc 0 (Real.pi / 2) :=
    ⟨terminalAngleDeficit_nonneg s, (terminalAngleDeficit_lt_pi_div_two
      (hsmall.trans_lt (by linarith))).le⟩
  have hspeed : deriv terminalAngleDeficit s ≤ 1 := by
    rw [deriv_terminalAngleDeficit]
    apply (deriv_angle_le _).trans
    apply (div_le_one (by positivity : 0 < Real.sqrt 2)).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hβsmall : terminalAngleDeficit s ≤ 1 / 2 :=
    (terminalAngleDeficit_le_mul_deriv hs.le).trans
      ((mul_le_of_le_one_right hs.le hspeed).trans hsmall)
  have hβsq : (terminalAngleDeficit s) ^ 2 ≤ 1 / 4 := by
    nlinarith [hβ.1]
  have hcos : 1 / 2 ≤ Real.cos (terminalAngleDeficit s) := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := terminalAngleDeficit s)]
  exact relative_log_cos_bounds hβ (deriv_terminalAngleDeficit_pos hs)
    (deriv_deriv_terminalAngleDeficit_nonneg s) hcos (terminalAngleDeficit_le_mul_deriv hs.le)

theorem exists_conformal_collar {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ z ∈ Ico (-2 * A) 0, conformalRadius z < transitionEnd) ∧
      (∀ z ∈ Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            ε * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < ε := by
  obtain ⟨d, hd, hnorm⟩ := exists_pos_intervalDerivativeNorm_lt
    contDiff_conformalFactor 2 0 (fun j _ => iteratedDeriv_conformalFactor_zero j) hε
  let τ : ℝ := min (1 / 2) (ε / 8)
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hc : ContinuousAt (fun z => transitionEnd - conformalRadius z) 0 :=
    continuousAt_const.sub contDiff_conformalRadius.continuous.continuousAt
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), transitionEnd - conformalRadius z < τ :=
    hc.eventually_lt_const (by simpa only [conformalRadius_zero, sub_self] using hτ)
  obtain ⟨e, he, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let A := min d (min e (1 / 4)) / 2
  have hA : 0 < A := half_pos (lt_min hd (lt_min he (by norm_num)))
  have hAd : A ≤ d := by dsimp [A]; linarith [min_le_left d (min e (1 / 4))]
  have hAe : A < e := by
    have hh := (min_le_right d (min e (1 / 4))).trans (min_le_left e (1 / 4))
    dsimp [A]
    linarith
  have hAsmall : 2 * A < 1 / 2 := by
    have hh := (min_le_right d (min e (1 / 4))).trans (min_le_right e (1 / 4))
    dsimp [A]
    linarith
  refine ⟨A, hA, hAsmall, fun z hz => conformalRadius_lt_transitionEnd hz.2, ?_, ?_⟩
  · intro z hz
    obtain ⟨hF, hF', hF''⟩ := conformalFactor_signs_of_neg hz.2
    refine ⟨hF, hF', hF'', ?_⟩
    let s := transitionEnd - conformalRadius z
    have hs : 0 < s := sub_pos.mpr (conformalRadius_lt_transitionEnd hz.2)
    have hsτ : s < τ := hnear (by
      rw [Real.dist_eq, sub_zero, abs_of_neg hz.2]
      linarith [hz.1])
    have hsmall : s ≤ 1 / 2 := hsτ.le.trans (min_le_left _ _)
    have hεs : 4 * s ≤ ε := by
      have hh := hsτ.le.trans (min_le_right _ _)
      linarith
    have hεs2 : 4 * s ^ 2 ≤ ε := by nlinarith
    have hb := terminal_relative_bounds hs hsmall
    dsimp only at hb
    rw [← conformalFactor_eq_terminalAngleDeficit,
      ← deriv_conformalFactor_eq_terminalAngleDeficit,
      ← neg_deriv_deriv_conformalFactor_eq_terminalAngleDeficit] at hb
    rw [abs_of_pos hF']
    exact max_le (hb.2.1.trans (mul_le_mul_of_nonneg_right hεs2 hb.1.le))
      (hb.2.2.trans (mul_le_mul_of_nonneg_right hεs hb.1.le))
  · simpa only [zero_sub] using hnorm A hA.le hAd

end DifferentialGeometry.PDE.RicciFlow.StandardCap
