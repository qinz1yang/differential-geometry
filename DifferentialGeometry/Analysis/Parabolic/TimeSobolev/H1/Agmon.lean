import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Energy

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] {T : ℝ}

theorem abs_norm_sq_sub_norm_sq_le (u : timeH1 X T) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    |‖u.toFun b‖ ^ 2 - ‖u.toFun a‖ ^ 2| ≤ 2 * ‖u.toFunL2‖ * ‖u.deriv‖ := by
  have hrep := TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
  have heq : (∫ t in a..b, inner ℝ (u.toFun t) (u.deriv t)) =
      ∫ t in a..b, inner ℝ (u.toFunL2 t) (u.deriv t) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : uIoc a b ⊆ Icc (0 : ℝ) T :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
    have hrep' : u.toFunL2 =ᵐ[volume.restrict (uIoc a b)] u.toFun :=
      hrep.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [ae_imp_of_ae_restrict hrep'] with t ht htab
    rw [ht htab]
  rw [u.norm_sq_sub_norm_sq_eq_two_intervalIntegral ha hb,
    intervalIntegral.integral_const_mul, heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |∫ t in a..b, inner ℝ (u.toFunL2 t) (u.deriv t)| ≤
        2 * (‖u.toFunL2‖ * ‖u.deriv‖) :=
      mul_le_mul_of_nonneg_left
        (TimeSobolev.abs_intervalIntegral_inner_le_norm u.toFunL2 u.deriv ha hb) (by norm_num)
    _ = 2 * ‖u.toFunL2‖ * ‖u.deriv‖ := by ring

theorem agmon_inequality (u : timeH1 X T) (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ^ 2 ≤ ‖u.toFunL2‖ ^ 2 / T + 2 * ‖u.toFunL2‖ * ‖u.deriv‖ := by
  have hrep := TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
  have hi : Integrable (fun s ↦ ‖u.toFunL2 s‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.toFunL2)).mp
      (Lp.memLp u.toFunL2)
  have hbound : ∀ᵐ s ∂timeMeasure T,
      ‖u.toFun t‖ ^ 2 ≤ ‖u.toFunL2 s‖ ^ 2 + 2 * ‖u.toFunL2‖ * ‖u.deriv‖ := by
    have hmem : ∀ᵐ s ∂timeMeasure T, s ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hrep, hmem] with s hs hsmem
    have hb := (le_abs_self _).trans (u.abs_norm_sq_sub_norm_sq_le hsmem ht)
    change u.toFunL2 s = u.toFun s at hs
    rw [hs]
    linarith
  have hint := integral_mono_ae (integrable_const (‖u.toFun t‖ ^ 2))
    (hi.add (integrable_const _)) hbound
  simp only [Pi.add_apply] at hint
  rw [integral_add hi (integrable_const _)] at hint
  have hnorm : (∫ s, ‖u.toFunL2 s‖ ^ 2 ∂timeMeasure T) = ‖u.toFunL2‖ ^ 2 :=
    (TimeSobolev.norm_sq_eq_integral u.toFunL2).symm
  rw [hnorm, integral_const, integral_const, timeMeasure_real_univ hT.le] at hint
  simp only [smul_eq_mul] at hint
  have hcancel : (‖u.toFunL2‖ ^ 2 / T) * T = ‖u.toFunL2‖ ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hT)
  nlinarith

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

namespace ContDiffOn

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] {T : ℝ} {f : ℝ → X}

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem agmon_inequality (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) T))
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖f t‖ ^ 2 ≤ (∫ s in Icc (0 : ℝ) T, ‖f s‖ ^ 2) / T +
      2 * Real.sqrt (∫ s in Icc (0 : ℝ) T, ‖f s‖ ^ 2) *
        Real.sqrt (∫ s in Icc (0 : ℝ) T, ‖deriv f s‖ ^ 2) := by
  let u := timeH1.ofContDiffOn hT.le f hf
  have hu : EqOn u.toFun f (Icc (0 : ℝ) T) := timeH1.toFun_ofContDiffOn hT.le f hf
  have hrep : u.toFunL2 =ᵐ[timeMeasure T] f := by
    have hmem : ∀ᵐ s ∂timeMeasure T, s ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [coeFn_ofContinuousOn u.continuousOn_toFun, hmem] with s hs hsmem
    exact hs.trans (hu hsmem)
  have hnorm : ‖u.toFunL2‖ = Real.sqrt (∫ s in Icc (0 : ℝ) T, ‖f s‖ ^ 2) := by
    rw [norm_eq_sqrt_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [hrep] with s hs using congrArg (fun x ↦ ‖x‖ ^ 2) hs
  have hnormsq : ‖u.toFunL2‖ ^ 2 = ∫ s in Icc (0 : ℝ) T, ‖f s‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hrep] with s hs using congrArg (fun x ↦ ‖x‖ ^ 2) hs
  have hderiv : ‖u.deriv‖ = Real.sqrt (∫ s in Icc (0 : ℝ) T, ‖deriv f s‖ ^ 2) := by
    rw [norm_eq_sqrt_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [timeH1.deriv_ofContDiffOn hT.le f hf] with s hs
    exact congrArg (fun x ↦ ‖x‖ ^ 2) hs
  have h := u.agmon_inequality hT ht
  rwa [hu ht, hnormsq, hnorm, hderiv] at h

end ContDiffOn
