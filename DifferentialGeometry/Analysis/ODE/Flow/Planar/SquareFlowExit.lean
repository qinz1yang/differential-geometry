import DifferentialGeometry.Analysis.ODE.Flow.Planar.PlanarEscape
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantHyperplaneFlow
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantHalfSpaceFlow

open Set Metric
open scoped ContDiff

namespace Poincare.Analysis

theorem exists_pos_rightEdge_crossing
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v z = 1)
    {z : ℂ} (hzre : z.re ∈ Ico 0 1) (hzim : z.im ∈ Icc 0 1) :
    ∃ t > 0, (φ t z).re = 1 := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
  have hlo (w : ℂ) (hw : w.im = 0) : v w = 1 := hfixed w (Or.inr (Or.inr (Or.inl hw.le)))
  have hhi (w : ℂ) (hw : w.im = 1) : v w = 1 := hfixed w (Or.inr (Or.inr (Or.inr hw.ge)))
  have hboundary (b : ℝ) (hline : ∀ w : ℂ, w.im = b → v w = 1) (hb : z.im = b) :
      ∃ t > 0, (φ t z).re = 1 := by
    have he := integralCurve_eq_translation_on_constant_hyperplane hv1 Complex.imCLM
      (1 : ℂ) (by simp) hline (hderiv z) (t := 0)
      (by simpa only [φ.map_zero_apply, Complex.imCLM_apply] using hb) (1 - z.re)
    rw [φ.map_zero_apply] at he
    refine ⟨1 - z.re, sub_pos.mpr hzre.2, ?_⟩
    rw [he]
    simp [Complex.real_smul]
  rcases eq_or_lt_of_le hzim.1 with hzero | hzero
  · exact hboundary 0 hlo hzero.symm
  rcases lt_or_eq_of_le hzim.2 with hone | hone
  · have hstrip (t : ℝ) : 0 < (φ t z).im ∧ (φ t z).im < 1 := by
      have lower := lt_iff_of_integralCurve_constant_hyperplane
        hv1 (-Complex.imCLM) 1 (by simp) (b := 0)
        (fun w hw ↦ hlo w (by simpa using hw)) (hderiv z) t 0
      have upper := lt_iff_of_integralCurve_constant_hyperplane
        hv1 Complex.imCLM 1 (by simp) hhi (hderiv z) t 0
      exact ⟨by simpa only [φ.map_zero_apply, neg_apply, Complex.imCLM_apply, neg_lt_zero]
        using lower.mpr (by simpa using hzero),
        upper.mpr (by simpa only [φ.map_zero_apply, Complex.imCLM_apply] using hone)⟩
    obtain ⟨t, ht, hout⟩ := exists_time_ge_not_mem_isCompact φ hv hnz hderiv
      (isCompact_closedBall (0 : ℂ) 2) z 0
    have hleft : 0 ≤ (φ t z).re :=
      le_of_integralCurve_constant_incoming_halfSpace hv Complex.reCLM (1 : ℂ)
        (by simp) (fun w hw ↦ hfixed w (Or.inl hw)) (hderiv z)
        (by simpa only [φ.map_zero_apply, Complex.reCLM_apply] using hzre.1) ht
    have hright : 1 < (φ t z).re := by
      by_contra h
      apply hout
      rw [mem_closedBall, dist_zero_right]
      calc
        ‖φ t z‖ ≤ |(φ t z).re| + |(φ t z).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 2 := by
          rw [abs_of_nonneg hleft, abs_of_nonneg (hstrip t).1.le]
          linarith [(hstrip t).2, le_of_not_gt h]
    obtain ⟨s, hs⟩ := intermediate_value_univ 0 t
      (Complex.continuous_re.comp (φ.continuous continuous_id continuous_const))
      (show (1 : ℝ) ∈ Icc (φ 0 z).re (φ t z).re from
        ⟨by simpa only [φ.map_zero_apply] using hzre.2.le, hright.le⟩)
    refine ⟨s, pos_of_integralCurve_constant_halfSpace_crossing hv Complex.reCLM
      (1 : ℂ) (by simp) (fun w hw ↦ hfixed w (Or.inr (Or.inl hw)))
      (hderiv z) (by simpa only [φ.map_zero_apply, Complex.reCLM_apply] using hzre.2) hs, hs⟩
  · exact hboundary 1 hhi hone

end Poincare.Analysis
