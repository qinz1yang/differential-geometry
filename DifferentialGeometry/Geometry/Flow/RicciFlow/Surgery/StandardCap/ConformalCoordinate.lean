import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Profile
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

def conformalCoordinate (r : ℝ) : ℝ :=
  Real.sqrt 2 * ∫ t in transitionEnd..r, (warpingFunction t)⁻¹

private theorem contDiffOn_inv_warpingFunction :
    ContDiffOn ℝ ∞ (fun r => (warpingFunction r)⁻¹) (Ioi 0) :=
  contDiff_warpingFunction.contDiffOn.inv (fun _ hr => (warpingFunction_pos hr).ne')

private theorem intervalIntegrable_inv_warpingFunction {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun r => (warpingFunction r)⁻¹) volume a b :=
  (contDiffOn_inv_warpingFunction.continuousOn.mono
    (fun _ ht => (lt_min ha hb).trans_le ht.1)).intervalIntegrable

theorem hasDerivAt_conformalCoordinate {r : ℝ} (hr : 0 < r) :
    HasDerivAt conformalCoordinate (Real.sqrt 2 / warpingFunction r) r := by
  have hc : ContinuousAt (fun r => (warpingFunction r)⁻¹) r :=
    (contDiffOn_inv_warpingFunction.contDiffAt (isOpen_Ioi.mem_nhds hr)).continuousAt
  change HasDerivAt (fun r => Real.sqrt 2 * ∫ t in transitionEnd..r, (warpingFunction t)⁻¹) _ r
  rw [div_eq_mul_inv]
  exact (intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_inv_warpingFunction transitionEnd_pos hr)
      (contDiff_warpingFunction.continuous.measurable.inv.aestronglyMeasurable.stronglyMeasurableAtFilter)
      hc).const_mul (Real.sqrt 2)

theorem deriv_conformalCoordinate {r : ℝ} (hr : 0 < r) :
    deriv conformalCoordinate r = Real.sqrt 2 / warpingFunction r :=
  (hasDerivAt_conformalCoordinate hr).deriv

theorem contDiffOn_conformalCoordinate : ContDiffOn ℝ ∞ conformalCoordinate (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  refine ⟨fun r hr => (hasDerivAt_conformalCoordinate hr).differentiableAt.differentiableWithinAt, ?_⟩
  apply ((contDiffOn_const (c := Real.sqrt 2)).mul contDiffOn_inv_warpingFunction).congr
  intro r hr
  simpa only [div_eq_mul_inv] using (deriv_conformalCoordinate hr)

theorem strictMonoOn_conformalCoordinate : StrictMonoOn conformalCoordinate (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) contDiffOn_conformalCoordinate.continuousOn
  intro r hr
  rw [interior_Ioi] at hr
  rw [deriv_conformalCoordinate hr]
  exact div_pos (Real.sqrt_pos.mpr (by norm_num)) (warpingFunction_pos hr)

@[simp] theorem conformalCoordinate_transitionEnd : conformalCoordinate transitionEnd = 0 := by
  simp [conformalCoordinate]

theorem conformalCoordinate_cylindrical {r : ℝ} (hr : transitionEnd ≤ r) :
    conformalCoordinate r = r - transitionEnd := by
  have heq : (∫ t in transitionEnd..r, (warpingFunction t)⁻¹) =
      ∫ t in transitionEnd..r, (Real.sqrt 2)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr] at ht
    change (warpingFunction t)⁻¹ = (Real.sqrt 2)⁻¹
    rw [warpingFunction_eq_sqrt_two ht.1]
  rw [conformalCoordinate, heq, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp

private theorem conformalCoordinate_le_log {r : ℝ} (hr : 0 < r) (hrL : r ≤ transitionEnd) :
    conformalCoordinate r ≤ Real.sqrt 2 * (Real.log r - Real.log transitionEnd) := by
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume r transitionEnd :=
    (continuousOn_inv₀.mono (fun t ht => ne_of_gt ((lt_min hr transitionEnd_pos).trans_le ht.1))).intervalIntegrable
  have hle : (∫ t in r..transitionEnd, t⁻¹) ≤ ∫ t in r..transitionEnd, (warpingFunction t)⁻¹ := by
    apply intervalIntegral.integral_mono_on hrL hi
      (intervalIntegrable_inv_warpingFunction hr transitionEnd_pos)
    intro t ht
    have htpos : 0 < t := hr.trans_le ht.1
    exact (inv_le_inv₀ htpos (warpingFunction_pos htpos)).mpr (warpingFunction_le htpos.le)
  have hlog : (∫ t in r..transitionEnd, t⁻¹) = Real.log transitionEnd - Real.log r := by
    rw [integral_inv_of_pos hr transitionEnd_pos, Real.log_div transitionEnd_pos.ne' hr.ne']
  rw [conformalCoordinate, intervalIntegral.integral_symm]
  rw [hlog] at hle
  have hm := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 2)
  nlinarith

private def logConformalCoordinate (t : ℝ) : ℝ := conformalCoordinate (Real.exp t)

private theorem contDiff_logConformalCoordinate : ContDiff ℝ ∞ logConformalCoordinate := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (contDiffOn_conformalCoordinate.contDiffAt
    (isOpen_Ioi.mem_nhds (Real.exp_pos t))).comp t Real.contDiff_exp.contDiffAt

private theorem strictMono_logConformalCoordinate : StrictMono logConformalCoordinate := by
  intro x y hxy
  exact strictMonoOn_conformalCoordinate (Real.exp_pos x) (Real.exp_pos y) (Real.exp_lt_exp.mpr hxy)

private theorem hasDerivAt_logConformalCoordinate (t : ℝ) :
    HasDerivAt logConformalCoordinate
      (Real.sqrt 2 / warpingFunction (Real.exp t) * Real.exp t) t :=
  (hasDerivAt_conformalCoordinate (Real.exp_pos t)).comp t (Real.hasDerivAt_exp t)

private theorem logConformalCoordinate_derivative_pos (t : ℝ) :
    0 < Real.sqrt 2 / warpingFunction (Real.exp t) * Real.exp t :=
  mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num))
    (warpingFunction_pos (Real.exp_pos t))) (Real.exp_pos t)

private theorem tendsto_logConformalCoordinate_atTop :
    Tendsto logConformalCoordinate atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop
    (max transitionEnd (b + transitionEnd)))] with t ht
  have hL : transitionEnd ≤ Real.exp t := (le_max_left _ _).trans ht
  change b ≤ conformalCoordinate (Real.exp t)
  rw [conformalCoordinate_cylindrical hL]
  linarith [le_max_right transitionEnd (b + transitionEnd)]

private theorem tendsto_logConformalCoordinate_atBot :
    Tendsto logConformalCoordinate atBot atBot := by
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [eventually_le_atBot
    (min (Real.log transitionEnd) (b / Real.sqrt 2 + Real.log transitionEnd))] with t ht
  have htL : t ≤ Real.log transitionEnd := ht.trans (min_le_left _ _)
  have heL : Real.exp t ≤ transitionEnd := by
    simpa only [Real.exp_log transitionEnd_pos] using Real.exp_le_exp.mpr htL
  have hbound := conformalCoordinate_le_log (Real.exp_pos t) heL
  rw [Real.log_exp] at hbound
  apply hbound.trans
  have hb : t - Real.log transitionEnd ≤ b / Real.sqrt 2 := by
    linarith [ht.trans (min_le_right _ _)]
  simpa only [mul_comm] using (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mp hb

private def logConformalHomeomorph : ℝ ≃ₜ ℝ :=
  (strictMono_logConformalCoordinate.orderIsoOfSurjective logConformalCoordinate
    (contDiff_logConformalCoordinate.continuous.surjective
      tendsto_logConformalCoordinate_atTop tendsto_logConformalCoordinate_atBot)).toHomeomorph

private theorem contDiff_logConformalHomeomorph_symm :
    ContDiff ℝ ∞ (logConformalHomeomorph.symm : ℝ → ℝ) :=
  logConformalHomeomorph.contDiff_symm_deriv
    (fun t => (logConformalCoordinate_derivative_pos t).ne')
    hasDerivAt_logConformalCoordinate contDiff_logConformalCoordinate

def conformalRadius (z : ℝ) : ℝ := Real.exp (logConformalHomeomorph.symm z)

theorem conformalRadius_pos (z : ℝ) : 0 < conformalRadius z := Real.exp_pos _

theorem contDiff_conformalRadius : ContDiff ℝ ∞ conformalRadius :=
  Real.contDiff_exp.comp contDiff_logConformalHomeomorph_symm

@[simp] theorem conformalCoordinate_conformalRadius (z : ℝ) :
    conformalCoordinate (conformalRadius z) = z :=
  logConformalHomeomorph.apply_symm_apply z

@[simp] theorem conformalRadius_conformalCoordinate {r : ℝ} (hr : 0 < r) :
    conformalRadius (conformalCoordinate r) = r := by
  have h := logConformalHomeomorph.symm_apply_apply (Real.log r)
  have h' : logConformalHomeomorph (Real.log r) = conformalCoordinate r := by
    change conformalCoordinate (Real.exp (Real.log r)) = _
    rw [Real.exp_log hr]
  rw [h'] at h
  rw [conformalRadius, h, Real.exp_log hr]

theorem strictMono_conformalRadius : StrictMono conformalRadius := by
  intro x y hxy
  apply lt_of_not_ge
  intro hge
  have h := strictMonoOn_conformalCoordinate.monotoneOn
    (conformalRadius_pos y) (conformalRadius_pos x) hge
  rw [conformalCoordinate_conformalRadius, conformalCoordinate_conformalRadius] at h
  exact (not_le.mpr hxy) h

@[simp] theorem conformalRadius_zero : conformalRadius 0 = transitionEnd := by
  rw [← conformalCoordinate_transitionEnd, conformalRadius_conformalCoordinate transitionEnd_pos]

theorem conformalRadius_cylindrical {z : ℝ} (hz : 0 ≤ z) :
    conformalRadius z = transitionEnd + z := by
  have hr : 0 < transitionEnd + z := by linarith [transitionEnd_pos]
  have h := conformalRadius_conformalCoordinate hr
  rw [conformalCoordinate_cylindrical (by linarith), add_sub_cancel_left] at h
  exact h

theorem hasDerivAt_conformalRadius (z : ℝ) :
    HasDerivAt conformalRadius (warpingFunction (conformalRadius z) / Real.sqrt 2) z := by
  have h := HasDerivAt.of_local_left_inverse contDiff_conformalRadius.continuous.continuousAt
    (hasDerivAt_conformalCoordinate (conformalRadius_pos z))
    (div_pos (Real.sqrt_pos.mpr (by norm_num))
      (warpingFunction_pos (conformalRadius_pos z))).ne'
    (Filter.Eventually.of_forall conformalCoordinate_conformalRadius)
  simpa only [inv_div] using h

theorem deriv_conformalRadius (z : ℝ) :
    deriv conformalRadius z = warpingFunction (conformalRadius z) / Real.sqrt 2 :=
  (hasDerivAt_conformalRadius z).deriv

end DifferentialGeometry.PDE.RicciFlow.StandardCap
