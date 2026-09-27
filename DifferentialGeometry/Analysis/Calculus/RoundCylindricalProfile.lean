import DifferentialGeometry.Analysis.Calculus.Cutoff.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.RoundCylindricalProfile

open Metric Filter
open scoped ContDiff Topology

private def radiusBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def roundRadius (r : ℝ) : ℝ :=
  2 * Real.sin (r / 2)

def cylinderRadius : ℝ :=
  2

def bumpRadius (r : ℝ) : ℝ :=
  radiusBump r * roundRadius r + (1 - radiusBump r) * cylinderRadius

theorem contDiff_bumpRadius : ContDiff ℝ (⊤ : ℕ∞) bumpRadius := by
  unfold bumpRadius roundRadius cylinderRadius
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (radiusBump : ℝ → ℝ) :=
    radiusBump.contDiff
  have hround : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => 2 * Real.sin (r / 2)) := by
    fun_prop
  have hone : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have htwo : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (2 : ℝ)) := contDiff_const
  exact (hcut.mul hround).add ((hone.sub hcut).mul htwo)

theorem bumpRadius_eq_roundRadius_of_dist_le {r : ℝ} (hr : dist r 0 ≤ 1) :
    bumpRadius r = roundRadius r := by
  have hmem : r ∈ closedBall (0 : ℝ) radiusBump.rIn := by
    simpa [radiusBump] using hr
  have hcut : radiusBump r = 1 := radiusBump.one_of_mem_closedBall hmem
  simp [bumpRadius, hcut]

theorem bumpRadius_eq_cylinderRadius_of_le_dist {r : ℝ} (hr : 2 ≤ dist r 0) :
    bumpRadius r = cylinderRadius := by
  have hcut : radiusBump r = 0 := radiusBump.zero_of_le_dist (by
    simpa [radiusBump] using hr)
  simp [bumpRadius, hcut]

@[simp] theorem bumpRadius_zero : bumpRadius 0 = 0 := by
  rw [bumpRadius_eq_roundRadius_of_dist_le (by simp)]
  simp [roundRadius]

private def transitionWidth : ℝ := 2 * (Real.pi - 1)

private theorem transitionWidth_pos : 0 < transitionWidth := by
  unfold transitionWidth
  nlinarith [Real.pi_gt_three]

def slope (r : ℝ) : ℝ :=
  1 - Real.smoothTransition ((r - 1) / transitionWidth)

theorem contDiff_slope : ContDiff ℝ (⊤ : ℕ∞) slope := by
  unfold slope transitionWidth
  fun_prop

theorem slope_eq_one_of_le {r : ℝ} (hr : r ≤ 1) : slope r = 1 := by
  unfold slope
  rw [Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) transitionWidth_pos.le

theorem slope_eq_zero_of_le {r : ℝ} (hr : 2 * Real.pi - 1 ≤ r) : slope r = 0 := by
  unfold slope
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ transitionWidth_pos]
    unfold transitionWidth
    linarith

theorem slope_mem_Icc (r : ℝ) : slope r ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold slope
    linarith [Real.smoothTransition.le_one ((r - 1) / transitionWidth)]
  · unfold slope
    linarith [Real.smoothTransition.nonneg ((r - 1) / transitionWidth)]

theorem antitone_slope : Antitone slope := by
  intro a b hab
  unfold slope
  have harg : (a - 1) / transitionWidth ≤ (b - 1) / transitionWidth := by
    rw [div_le_div_iff_of_pos_right transitionWidth_pos]
    linarith
  linarith [Real.smoothTransition.monotone harg]

def phase (r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, slope s

theorem hasDerivAt_phase (r : ℝ) : HasDerivAt phase (slope r) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    (contDiff_slope.continuous.intervalIntegrable 0 r)
    contDiff_slope.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    contDiff_slope.continuous.continuousAt

theorem deriv_phase : deriv phase = slope :=
  funext fun r => (hasDerivAt_phase r).deriv

theorem contDiff_phase : ContDiff ℝ (⊤ : ℕ∞) phase := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · exact intervalIntegral.differentiable_integral_of_continuous contDiff_slope.continuous
  · rw [deriv_phase]
    exact contDiff_slope

theorem concaveOn_phase : ConcaveOn ℝ Set.univ phase := by
  apply Antitone.concaveOn_univ_of_deriv (contDiff_phase.differentiable (by simp))
  rw [deriv_phase]
  exact antitone_slope

theorem phase_eq_self_of_le {r : ℝ} (hr : r ≤ 1) : phase r = r := by
  unfold phase
  calc
    (∫ x in (0 : ℝ)..r, slope x) = ∫ _x in (0 : ℝ)..r, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply slope_eq_one_of_le
      rcases Set.mem_uIcc.mp hx with hx | hx
      · exact hx.2.trans hr
      · exact hx.2.trans zero_le_one
    _ = r := by simp

def radius (r : ℝ) : ℝ :=
  2 * Real.sin (phase r / 2)

theorem contDiff_radius : ContDiff ℝ (⊤ : ℕ∞) radius := by
  unfold radius
  have hhalf : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => phase r / 2) := by
    simpa only [div_eq_mul_inv] using
      contDiff_phase.mul (contDiff_const :
        ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (2 : ℝ)⁻¹))
  exact contDiff_const.mul (Real.contDiff_sin.comp hhalf)

theorem radius_eq_roundRadius_of_le {r : ℝ} (hr : r ≤ 1) : radius r = roundRadius r := by
  simp only [radius, roundRadius, phase_eq_self_of_le hr]

def transitionEnd : ℝ := 2 * Real.pi - 1

theorem transitionEnd_pos : 0 < transitionEnd := by
  unfold transitionEnd
  nlinarith [Real.pi_gt_three]

theorem phase_transitionEnd : phase transitionEnd = Real.pi := by
  have hcont := contDiff_slope.continuous
  have hfirst : (∫ x in (0 : ℝ)..1, slope x) = 1 :=
    phase_eq_self_of_le le_rfl
  have hsecond : (∫ x in (1 : ℝ)..transitionEnd, slope x) = Real.pi - 1 := by
    unfold slope
    rw [show transitionWidth = transitionEnd - 1 by
      unfold transitionWidth transitionEnd
      ring]
    have ht : Continuous (fun x : ℝ =>
        Real.smoothTransition ((x - 1) / (transitionEnd - 1))) := by fun_prop
    rw [intervalIntegral.integral_sub intervalIntegrable_const (ht.intervalIntegrable _ _)]
    rw [Real.smoothTransition.integral_comp_sub_div]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    unfold transitionEnd
    ring
  unfold phase
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 transitionEnd)]
  rw [hfirst, hsecond]
  ring

theorem phase_eq_pi_of_le {r : ℝ} (hr : transitionEnd ≤ r) : phase r = Real.pi := by
  have hcont := contDiff_slope.continuous
  have hzero : (∫ x in transitionEnd..r, slope x) = 0 := by
    calc
      (∫ x in transitionEnd..r, slope x) = ∫ _x in transitionEnd..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply slope_eq_zero_of_le
        rw [Set.uIcc_of_le hr] at hx
        exact hx.1
      _ = 0 := by simp
  unfold phase
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 transitionEnd) (hcont.intervalIntegrable transitionEnd r)]
  rw [show (∫ x in (0 : ℝ)..transitionEnd, slope x) = Real.pi from phase_transitionEnd,
    hzero, add_zero]

theorem monotone_phase : Monotone phase := by
  apply monotone_of_deriv_nonneg (contDiff_phase.differentiable (by simp))
  intro r
  rw [deriv_phase]
  exact (slope_mem_Icc r).1

theorem phase_mem_Icc {r : ℝ} (hr : 0 ≤ r) : phase r ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · simpa [phase] using monotone_phase hr
  · by_cases hre : r ≤ transitionEnd
    · simpa [phase_transitionEnd] using monotone_phase hre
    · rw [phase_eq_pi_of_le (le_of_not_ge hre)]

theorem radius_eq_cylinderRadius_of_le {r : ℝ} (hr : transitionEnd ≤ r) :
    radius r = cylinderRadius := by
  simp [radius, cylinderRadius, phase_eq_pi_of_le hr]

theorem hasDerivAt_radius (r : ℝ) :
    HasDerivAt radius (Real.cos (phase r / 2) * slope r) r := by
  have hphase := (hasDerivAt_phase r).div_const 2
  have hsin := hphase.sin.const_mul 2
  convert hsin using 1 <;> first | rfl | ring

theorem deriv_radius (r : ℝ) :
    deriv radius r = Real.cos (phase r / 2) * slope r :=
  (hasDerivAt_radius r).deriv

theorem deriv_radius_mem_Icc {r : ℝ} (hr : 0 ≤ r) :
    deriv radius r ∈ Set.Icc (0 : ℝ) 1 := by
  rw [deriv_radius]
  have hp := phase_mem_Icc hr
  have hcos0 : 0 ≤ Real.cos (phase r / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hp.1, Real.pi_pos], by nlinarith [hp.2]⟩
  have hcos1 : Real.cos (phase r / 2) ≤ 1 := Real.cos_le_one _
  have hs := slope_mem_Icc r
  constructor
  · exact mul_nonneg hcos0 hs.1
  · calc
      Real.cos (phase r / 2) * slope r ≤ 1 * slope r :=
        mul_le_mul_of_nonneg_right hcos1 hs.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hs.2 zero_le_one
      _ = 1 := mul_one 1

theorem antitoneOn_deriv_radius :
    AntitoneOn (deriv radius) (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  rw [deriv_radius, deriv_radius]
  have hpa := phase_mem_Icc ha
  have hpb := phase_mem_Icc hb
  have hphase : phase a / 2 ≤ phase b / 2 := by
    exact div_le_div_of_nonneg_right (monotone_phase hab) (by norm_num)
  have hcos : Real.cos (phase b / 2) ≤ Real.cos (phase a / 2) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (by nlinarith [hpa.1]) (by nlinarith [hpb.2, Real.pi_pos]) hphase
  have hcos0 : 0 ≤ Real.cos (phase a / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hpa.1, Real.pi_pos], by nlinarith [hpa.2]⟩
  exact mul_le_mul hcos (antitone_slope hab) (slope_mem_Icc b).1 hcos0

theorem concaveOn_radius : ConcaveOn ℝ (Set.Ici (0 : ℝ)) radius := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    contDiff_radius.continuous.continuousOn
    ((contDiff_radius.differentiable (by simp)).differentiableOn.mono interior_subset)
  exact antitoneOn_deriv_radius.mono interior_subset

theorem radius_pos {r : ℝ} (hr : 0 < r) : 0 < radius r := by
  have hphase0 : 0 < phase r := by
    by_cases hr1 : r ≤ 1
    · rw [phase_eq_self_of_le hr1]
      exact hr
    · have hmono := monotone_phase (le_of_not_ge hr1)
      rw [phase_eq_self_of_le le_rfl] at hmono
      linarith
  have hp := phase_mem_Icc hr.le
  have hsin : 0 < Real.sin (phase r / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith [hp.2, Real.pi_pos]⟩
  unfold radius
  positivity

def radialCurvatureCoefficient (r : ℝ) : ℝ :=
  -deriv (deriv radius) r / radius r

def tangentialCurvatureCoefficient (r : ℝ) : ℝ :=
  (1 - (deriv radius r) ^ 2) / radius r ^ 2

theorem radialCurvatureCoefficient_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ radialCurvatureCoefficient r := by
  have hanti : AntitoneOn (deriv radius) (Set.Ioi 0) :=
    antitoneOn_deriv_radius.mono (by
      intro x hx
      exact Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)
  have hsecond := hanti.derivWithin_nonpos (x := r)
  rw [derivWithin_of_mem_nhds (Ioi_mem_nhds hr)] at hsecond
  exact div_nonneg (neg_nonneg.mpr hsecond) (radius_pos hr).le

theorem tangentialCurvatureCoefficient_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ tangentialCurvatureCoefficient r := by
  have hd := deriv_radius_mem_Icc hr.le
  have hsq : (deriv radius r) ^ 2 ≤ 1 := by
    nlinarith [hd.1, hd.2]
  exact div_nonneg (sub_nonneg.mpr hsq) (sq_nonneg _)

theorem deriv_radius_of_le_one {r : ℝ} (hr : r ≤ 1) :
    deriv radius r = Real.cos (r / 2) := by
  rw [deriv_radius, phase_eq_self_of_le hr, slope_eq_one_of_le hr, mul_one]

theorem deriv_deriv_radius_of_le_one {r : ℝ} (hr : r ≤ 1) :
    deriv (deriv radius) r = -Real.sin (r / 2) / 2 := by
  have heq : Set.EqOn (deriv (deriv radius)) (fun x : ℝ => -Real.sin (x / 2) / 2)
      (Set.Iio 1) := by
    intro x hx
    have hgerm : deriv radius =ᶠ[nhds x] (fun y : ℝ => Real.cos (y / 2)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact deriv_radius_of_le_one hy.le
    rw [hgerm.deriv_eq]
    convert (Real.hasDerivAt_cos (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2) |>.deriv using 1 <;> first | rfl | ring
  have hcont : Continuous (deriv (deriv radius)) :=
    (contDiff_radius.iterate_deriv 2).continuous
  exact heq.closure hcont (by fun_prop) (by simpa only [closure_Iio, Set.mem_Iic] using hr)

theorem deriv_radius_of_transitionEnd_le {r : ℝ} (hr : transitionEnd ≤ r) :
    deriv radius r = 0 := by
  rw [deriv_radius, slope_eq_zero_of_le (by simpa [transitionEnd] using hr), mul_zero]

theorem deriv_deriv_radius_of_transitionEnd_le {r : ℝ} (hr : transitionEnd ≤ r) :
    deriv (deriv radius) r = 0 := by
  have heq : Set.EqOn (deriv (deriv radius)) (fun _ : ℝ => 0)
      (Set.Ioi transitionEnd) := by
    intro x hx
    have hgerm : deriv radius =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact deriv_radius_of_transitionEnd_le hy.le
    rw [hgerm.deriv_eq]
    simp
  have hcont : Continuous (deriv (deriv radius)) :=
    (contDiff_radius.iterate_deriv 2).continuous
  exact heq.closure hcont continuous_const (by simpa only [closure_Ioi, Set.mem_Ici] using hr)

theorem radialCurvatureCoefficient_eq_one_div_four_of_le_one {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    radialCurvatureCoefficient r = (1 : ℝ) / 4 := by
  have hpos := radius_pos hr
  rw [radius_eq_roundRadius_of_le hr1, roundRadius] at hpos
  have hsin : 0 < Real.sin (r / 2) := by nlinarith
  rw [radialCurvatureCoefficient, deriv_deriv_radius_of_le_one hr1,
    radius_eq_roundRadius_of_le hr1, roundRadius]
  field_simp [ne_of_gt hsin]
  ring

theorem tangentialCurvatureCoefficient_eq_one_div_four_of_le_one {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    tangentialCurvatureCoefficient r = (1 : ℝ) / 4 := by
  have hpos := radius_pos hr
  rw [radius_eq_roundRadius_of_le hr1, roundRadius] at hpos
  have hsin : 0 < Real.sin (r / 2) := by nlinarith
  have htrig := Real.sin_sq_add_cos_sq (r / 2)
  rw [tangentialCurvatureCoefficient, deriv_radius_of_le_one hr1,
    radius_eq_roundRadius_of_le hr1, roundRadius]
  field_simp [ne_of_gt hsin]
  nlinarith

theorem radialCurvatureCoefficient_eq_zero_of_transitionEnd_le {r : ℝ}
    (hr : transitionEnd ≤ r) : radialCurvatureCoefficient r = 0 := by
  rw [radialCurvatureCoefficient, deriv_deriv_radius_of_transitionEnd_le hr,
    radius_eq_cylinderRadius_of_le hr, cylinderRadius]
  norm_num

theorem tangentialCurvatureCoefficient_eq_one_div_four_of_transitionEnd_le {r : ℝ}
    (hr : transitionEnd ≤ r) :
    tangentialCurvatureCoefficient r = (1 : ℝ) / 4 := by
  rw [tangentialCurvatureCoefficient, deriv_radius_of_transitionEnd_le hr,
    radius_eq_cylinderRadius_of_le hr, cylinderRadius]
  norm_num

end DifferentialGeometry.Analysis.RoundCylindricalProfile
