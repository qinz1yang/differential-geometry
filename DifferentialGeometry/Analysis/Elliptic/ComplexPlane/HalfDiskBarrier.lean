import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Complex Filter Set InnerProductSpace Metric
open scoped Topology

namespace DifferentialGeometry.Analysis

noncomputable def halfDiskBarrier (R : ℝ) (z : ℂ) : ℝ :=
  R * z.im / ‖(R : ℂ) - z‖ ^ 2 + R * z.im / ‖(R : ℂ) + z‖ ^ 2

theorem halfDiskBarrier_eq_im (R : ℝ) (z : ℂ) :
    halfDiskBarrier R z = ((R : ℂ) / (R - z) - (R : ℂ) / (R + z)).im := by
  simp [halfDiskBarrier, Complex.div_im, Complex.normSq_eq_norm_sq]
  ring

theorem halfDiskBarrier_nonneg {R : ℝ} {z : ℂ} (hR : 0 ≤ R) (hz : 0 ≤ z.im) :
    0 ≤ halfDiskBarrier R z := by
  exact add_nonneg (div_nonneg (mul_nonneg hR hz) (sq_nonneg _))
    (div_nonneg (mul_nonneg hR hz) (sq_nonneg _))

theorem halfDiskBarrier_eq_zero_of_im_eq_zero {R : ℝ} {z : ℂ} (hz : z.im = 0) :
    halfDiskBarrier R z = 0 := by simp [halfDiskBarrier, hz]

theorem harmonicAt_halfDiskBarrier {R : ℝ} {z : ℂ}
    (hm : (R : ℂ) - z ≠ 0) (hp : (R : ℂ) + z ≠ 0) :
    HarmonicAt (halfDiskBarrier R) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => (R : ℂ) / (R - w) - (R : ℂ) / (R + w)) z :=
    (analyticAt_const.div (analyticAt_const.sub analyticAt_id) hm).sub
      (analyticAt_const.div (analyticAt_const.add analyticAt_id) hp)
  simpa only [← halfDiskBarrier_eq_im] using ha.harmonicAt_im

theorem lowerSemicontinuousOn_halfDiskBarrier {R : ℝ} (hR : 0 ≤ R) :
    LowerSemicontinuousOn (halfDiskBarrier R) {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  by_cases hm : (R : ℂ) - z = 0
  · have hz0 : z.im = 0 := by have hh := congrArg Complex.im hm; simpa using hh
    intro a ha
    rw [halfDiskBarrier_eq_zero_of_im_eq_zero hz0] at ha
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact ha.trans_le (halfDiskBarrier_nonneg hR hw)
  by_cases hp : (R : ℂ) + z = 0
  · have hz0 : z.im = 0 := by have hh := congrArg Complex.im hp; simpa using hh
    intro a ha
    rw [halfDiskBarrier_eq_zero_of_im_eq_zero hz0] at ha
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact ha.trans_le (halfDiskBarrier_nonneg hR hw)
  exact (harmonicAt_halfDiskBarrier hm hp).1.continuousAt.continuousWithinAt.lowerSemicontinuousWithinAt

theorem halfDiskBarrier_le {R r : ℝ} {z : ℂ}
    (hRr : r < R) (hz : ‖z‖ ≤ r) (hi : 0 ≤ z.im) :
    halfDiskBarrier R z ≤ (2 * R / (R - r) ^ 2) * z.im := by
  have hR : 0 ≤ R := (norm_nonneg z).trans (hz.trans hRr.le)
  have hn : 0 ≤ R * z.im := mul_nonneg hR hi
  have hpos : 0 < R - r := sub_pos.mpr hRr
  have hm : R - r ≤ ‖(R : ℂ) - z‖ := by
    have h := norm_sub_norm_le (R : ℂ) z
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR] at h
    linarith
  have hp : R - r ≤ ‖(R : ℂ) + z‖ := by
    have h := norm_sub_norm_le (R : ℂ) (-z)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, norm_neg,
      sub_neg_eq_add] at h
    linarith
  have hms : (R - r) ^ 2 ≤ ‖(R : ℂ) - z‖ ^ 2 :=
    (sq_le_sq₀ hpos.le (norm_nonneg _)).2 hm
  have hps : (R - r) ^ 2 ≤ ‖(R : ℂ) + z‖ ^ 2 :=
    (sq_le_sq₀ hpos.le (norm_nonneg _)).2 hp
  calc
    halfDiskBarrier R z ≤ R * z.im / (R - r) ^ 2 + R * z.im / (R - r) ^ 2 :=
      add_le_add (div_le_div_of_nonneg_left hn (sq_pos_of_pos hpos) hms)
        (div_le_div_of_nonneg_left hn (sq_pos_of_pos hpos) hps)
    _ = (2 * R / (R - r) ^ 2) * z.im := by ring

theorem halfDiskBarrier_eq_div_im_of_norm_eq {R : ℝ} {z : ℂ}
    (hz : ‖z‖ = R) (hi : 0 < z.im) :
    halfDiskBarrier R z = R / z.im := by
  have hR : 0 < R := hi.trans_le ((Complex.im_le_norm z).trans hz.le)
  have hsq : z.re ^ 2 + z.im ^ 2 = R ^ 2 := by
    calc
      _ = Complex.normSq z := by simp [Complex.normSq_apply, sq]
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = R ^ 2 := by rw [hz]
  have hm0 : (R : ℂ) - z ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at hh
    exact hi.ne' hh
  have hp0 : (R : ℂ) + z ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im, zero_add] at hh
    exact hi.ne' hh
  have hm : ‖(R : ℂ) - z‖ ^ 2 = 2 * R * (R - z.re) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    nlinarith [hsq]
  have hp : ‖(R : ℂ) + z‖ ^ 2 = 2 * R * (R + z.re) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im]
    nlinarith [hsq]
  have hmne : R - z.re ≠ 0 := by
    intro h
    have hh : ‖(R : ℂ) - z‖ ^ 2 = 0 := by rw [hm, h, mul_zero]
    exact hm0 (norm_eq_zero.mp (sq_eq_zero_iff.mp hh))
  have hpne : R + z.re ≠ 0 := by
    intro h
    have hh : ‖(R : ℂ) + z‖ ^ 2 = 0 := by rw [hp, h, mul_zero]
    exact hp0 (norm_eq_zero.mp (sq_eq_zero_iff.mp hh))
  rw [halfDiskBarrier, hm, hp]
  field_simp
  nlinarith [hsq]

end DifferentialGeometry.Analysis
