import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.LogKernel



noncomputable section

open scoped Topology ContDiff ComplexConjugate RealInnerProductSpace

namespace DifferentialGeometry.Analysis


theorem disk_log_boundary_denominator {w z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - conj w * z‖ ^ 2 = ‖z - w‖ ^ 2 := by
  have hzs : z.re * z.re + z.im * z.im = 1 := by
    simpa only [Complex.normSq_apply, hz, one_pow] using (Complex.normSq_eq_norm_sq z)
  have hm := congrArg (fun x : ℝ => x * (w.re * w.re + w.im * w.im)) hzs
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  nlinarith [hm]


theorem disk_log_boundary_numerator {w z : ℂ} (hz : ‖z‖ = 1) :
    inner ℝ (z - w) z + inner ℝ (1 - conj w * z) (-(conj w * z)) = ‖z - w‖ ^ 2 := by
  have hzs : z.re * z.re + z.im * z.im = 1 := by
    simpa only [Complex.normSq_apply, hz, one_pow] using (Complex.normSq_eq_norm_sq z)
  have hm := congrArg (fun x : ℝ => x * (w.re * w.re + w.im * w.im)) hzs
  simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply, RCLike.re_eq_complex_re, Complex.sq_norm,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  nlinarith [hm]




theorem hasDerivAt_diskNeumannLogKernel_radial {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ = 1) :
    HasDerivAt (fun r : ℝ => diskNeumannLogKernel w (r • z)) 1 1 := by
  have hzw : z - w ≠ 0 := by
    intro he
    have h := congrArg norm (sub_eq_zero.mp he)
    linarith
  have himage : 1 - conj w * z ≠ 0 :=
    diskImageLogKernel_argument_ne_zero (by simpa only [hz, mul_one] using hw)
  have hr : HasDerivAt (fun r : ℝ => r • z) z 1 := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id (1 : ℝ)).smul_const z
  have h₁ := hasDerivAt_log_norm_complex (hr.sub_const w)
    (show (1 : ℝ) • z - w ≠ 0 by simpa only [one_smul] using hzw)
  have h₂ := hasDerivAt_log_norm_complex ((hr.const_mul (conj w)).const_sub 1)
    (show 1 - conj w * ((1 : ℝ) • z) ≠ 0 by simpa only [one_smul] using himage)
  have hsum := h₁.add h₂
  simp only [one_smul] at hsum
  have hden : ‖z - w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hzw)
  have hvalue : inner ℝ (z - w) z / ‖z - w‖ ^ 2 +
      inner ℝ (1 - conj w * z) (-(conj w * z)) / ‖1 - conj w * z‖ ^ 2 = 1 := by
    rw [disk_log_boundary_denominator hz, ← add_div, disk_log_boundary_numerator hz,
      div_self hden]
  rw [hvalue] at hsum
  exact hsum

end DifferentialGeometry.Analysis
