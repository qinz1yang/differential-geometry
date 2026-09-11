import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem expNegInvGlue_div_eq_exp {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    expNegInvGlue (s / b) = Real.exp (-b / s) := by
  rw [expNegInvGlue, if_neg (div_pos hs hb).not_ge]
  congr 1
  field_simp

private theorem denominator_hasDerivAt {b s : ℝ} (hb : b ≠ 0) (hs : s ≠ 0) (a : ℝ) :
    HasDerivAt (fun t => a * (t ^ 2 / b) * expNegInvGlue (t / b))
      (a * (1 + 2 * s / b) * expNegInvGlue (s / b)) s := by
  have hgl : HasDerivAt expNegInvGlue
      ((s / b)⁻¹ ^ 2 * expNegInvGlue (s / b)) (s / b) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 (s / b)
  have hcomp := hgl.comp s ((hasDerivAt_id s).div_const b)
  convert! ((((hasDerivAt_id s).pow 2).div_const b).const_mul a).mul hcomp using 1
  simp only [Function.comp_apply, id_eq, Pi.pow_apply, Nat.cast_ofNat, mul_one]
  field_simp
  ring

theorem tendsto_integral_mul_expNegInvGlue_div {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Icc 0 δ)) (hc0 : c 0 ≠ 0) :
    Tendsto (fun s => (∫ u in (0 : ℝ)..s, c u * expNegInvGlue (u / b)) /
      (c 0 * (s ^ 2 / b) * Real.exp (-b / s))) (𝓝[>] 0) (𝓝 1) := by
  have hgl : Continuous (fun s : ℝ => expNegInvGlue (s / b)) :=
    (expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp (continuous_id.div_const b)
  have hnum : ContinuousOn (fun s => c s * expNegInvGlue (s / b)) (Icc 0 δ) :=
    hc.mul hgl.continuousOn
  have hff : ∀ s ∈ Ioo 0 δ,
      HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, c u * expNegInvGlue (u / b))
        (c s * expNegInvGlue (s / b)) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hnum.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le
    · exact (hnum.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    · exact (hnum s (Ioo_subset_Icc_self hs)).continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hgg : ∀ s ∈ Ioo 0 δ,
      HasDerivAt (fun t => c 0 * (t ^ 2 / b) * expNegInvGlue (t / b))
        (c 0 * (1 + 2 * s / b) * expNegInvGlue (s / b)) s :=
    fun s hs => denominator_hasDerivAt hb.ne' hs.1.ne' (c 0)
  have hg' : ∀ s ∈ Ioo 0 δ,
      c 0 * (1 + 2 * s / b) * expNegInvGlue (s / b) ≠ 0 := by
    intro s hs
    exact mul_ne_zero (mul_ne_zero hc0
      (ne_of_gt (add_pos zero_lt_one (div_pos (mul_pos (by norm_num) hs.1) hb))))
      (expNegInvGlue.pos_of_pos (div_pos hs.1 hb)).ne'
  have hprim : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, c u * expNegInvGlue (u / b))
      (Icc 0 δ) := by
    simpa only [uIcc_of_le hδ.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        (hnum.intervalIntegrable_of_Icc hδ.le) (left_mem_uIcc : 0 ∈ uIcc (0 : ℝ) δ))
  have hden : Continuous (fun s : ℝ => c 0 * (s ^ 2 / b) * expNegInvGlue (s / b)) :=
    (continuous_const.mul ((continuous_id.pow 2).div_const b)).mul hgl
  have hclim : Tendsto c (𝓝[>] 0) (𝓝 (c 0)) := by
    have h := ((hc 0 ⟨le_rfl, hδ.le⟩).mono Ioo_subset_Icc_self).tendsto
    rwa [nhdsWithin_Ioo_eq_nhdsGT hδ] at h
  have hbasic : Tendsto (fun s : ℝ => c s / (c 0 * (1 + 2 * s / b)))
      (𝓝[>] 0) (𝓝 1) := by
    have hd : Tendsto (fun s : ℝ => c 0 * (1 + 2 * s / b)) (𝓝[>] 0) (𝓝 (c 0)) := by
      have hcont : Continuous (fun s : ℝ => c 0 * (1 + 2 * s / b)) := by fun_prop
      have h := hcont.tendsto (0 : ℝ)
      convert! h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left) using 1
      simp only [mul_zero, zero_div, add_zero, mul_one]
    simpa only [Pi.div_def, div_self hc0] using hclim.div hd hc0
  have hquot : Tendsto (fun s => (c s * expNegInvGlue (s / b)) /
      (c 0 * (1 + 2 * s / b) * expNegInvGlue (s / b))) (𝓝[>] 0) (𝓝 1) := by
    apply hbasic.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (mul_div_mul_right _ _ (expNegInvGlue.pos_of_pos (div_pos hs hb)).ne').symm
  have hmain := HasDerivAt.lhopital_zero_right_on_Ico hδ hff hgg
    (hprim.mono Ico_subset_Icc_self) hden.continuousOn hg'
    (by simp) (by simp) hquot
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [expNegInvGlue_div_eq_exp hb hs]

end DifferentialGeometry.Analysis
