import DifferentialGeometry.Analysis.Integration.PolarDisk
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private def realTestDbar (φ : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2

private theorem locallyIntegrable_cauchyKernel_zero :
    LocallyIntegrable (fun z : ℂ => ((Real.pi : ℂ) * z)⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow
    (C := Real.pi⁻¹) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex])
  · exact Eventually.of_forall fun z => by
      simp only [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Real.rpow_neg_one, mul_inv_rev, mul_comm, le_refl]
  · exact (measurable_const.mul measurable_id).inv.aestronglyMeasurable

/-- The actual translated planar Cauchy kernel is locally Bochner integrable.
The totalized inverse at its single singular point does not affect the integral. -/
theorem locallyIntegrable_cauchyKernel (w : ℂ) :
    LocallyIntegrable (fun z : ℂ => ((Real.pi : ℂ) * (z - w))⁻¹) := by
  rw [locallyIntegrable_iff]
  intro s hs
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-w)
  have hm : MeasurePreserving e volume volume :=
    measurePreserving_add_right volume (-w)
  have hi := locallyIntegrable_cauchyKernel_zero.integrableOn_isCompact
    (hs.image e.continuous)
  have h := (hm.integrableOn_comp_preimage e.measurableEmbedding).mpr hi
  rw [Set.preimage_image_eq _ e.injective] at h
  simpa only [Function.comp_def, e, Homeomorph.coe_addRight, sub_eq_add_neg] using h

private theorem continuous_realTestDbar {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (realTestDbar φ) := by
  have hd := hφ.continuous_fderiv (by norm_num)
  exact ((Complex.continuous_ofReal.comp (hd.clm_apply continuous_const)).add
    (continuous_const.mul
      (Complex.continuous_ofReal.comp (hd.clm_apply continuous_const)))).div_const 2

private theorem compactSupport_realTestDbar {φ : ℂ → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (realTestDbar φ) := by
  apply HasCompactSupport.intro hc.isCompact
  intro z hz
  simp only [realTestDbar, fderiv_of_notMem_tsupport ℝ hz, _root_.zero_apply,
    Complex.ofReal_zero, mul_zero, add_zero, zero_div]

private theorem integrable_kernel_realTestDbar {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (w : ℂ) :
    Integrable (fun z : ℂ => ((Real.pi : ℂ) * (z - w))⁻¹ * realTestDbar φ z) := by
  exact (locallyIntegrable_cauchyKernel w).integrable_smul_right_of_hasCompactSupport
    (continuous_realTestDbar hφ) (compactSupport_realTestDbar hc)

private def radialTest (φ : ℂ → ℝ) (r θ : ℝ) : ℝ :=
  fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ)

private def angularTest (φ : ℂ → ℝ) (r θ : ℝ) : ℝ :=
  fderiv ℝ φ (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)

private theorem continuous_radialTest {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (fun q : ℝ × ℝ => radialTest φ q.1 q.2) := by
  have hp : Continuous (fun q : ℝ × ℝ => circleMap 0 q.1 q.2) := by
    unfold circleMap
    fun_prop
  have hu : Continuous (fun q : ℝ × ℝ => circleMap 0 1 q.2) := by
    fun_prop
  exact ((hφ.continuous_fderiv (by norm_num)).comp hp).clm_apply hu

private theorem continuous_angularTest {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (fun q : ℝ × ℝ => angularTest φ q.1 q.2) := by
  have hp : Continuous (fun q : ℝ × ℝ => circleMap 0 q.1 q.2) := by
    unfold circleMap
    fun_prop
  have hu : Continuous (fun q : ℝ × ℝ => Complex.I * circleMap 0 1 q.2) := by
    fun_prop
  exact ((hφ.continuous_fderiv (by norm_num)).comp hp).clm_apply hu

private theorem circleMap_eq_smul_unit (r θ : ℝ) :
    circleMap 0 r θ = r • circleMap 0 1 θ := by
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]

private theorem hasDerivAt_radialTest {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => φ (circleMap 0 s θ)) (radialTest φ r θ) r := by
  have hp : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r := by
    rw [show (fun s : ℝ => circleMap 0 s θ) = (fun s : ℝ => s • circleMap 0 1 θ)
      from funext fun s => circleMap_eq_smul_unit s θ]
    simpa only [one_smul, id_eq] using
      (hasDerivAt_id r).smul_const (circleMap 0 1 θ)
  exact (hφ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r hp

private theorem hasDerivAt_angularTest {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => φ (circleMap 0 r t)) (r * angularTest φ r θ) θ := by
  have h := (hφ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap 0 r θ)
  have hvec : circleMap 0 r θ * Complex.I = r • (Complex.I * circleMap 0 1 θ) := by
    rw [circleMap_eq_smul_unit r θ, smul_mul_assoc, mul_comm (circleMap 0 1 θ) Complex.I]
  have he : fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) =
      r * angularTest φ r θ := by
    rw [hvec, map_smul]
    rfl
  exact he ▸ h

private theorem integral_Ioo_eq_interval {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {a b : ℝ} (hab : a ≤ b) (f : ℝ → F) :
    (∫ x in Ioo a b, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

private theorem integral_angularTest_eq_zero {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi, angularTest φ r θ) = 0 := by
  have hcont : Continuous (fun θ : ℝ => angularTest φ r θ) :=
    (continuous_angularTest hφ).comp (continuous_const.prodMk continuous_id)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_angularTest hφ r θ)
    ((continuous_const.mul hcont).intervalIntegrable (-Real.pi) Real.pi)
  rw [intervalIntegral.integral_const_mul] at h
  have he : circleMap 0 r Real.pi = circleMap 0 r (-Real.pi) := by
    simp [circleMap, Complex.exp_mul_I]
  rw [he, sub_self] at h
  rw [integral_Ioo_eq_interval (by linarith [Real.pi_pos])]
  exact (mul_eq_zero.mp h).resolve_left hr.ne'

private theorem realLinear_apply_complex (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    (L z : ℂ) = (z.re : ℂ) * (L (1 : ℂ) : ℂ) +
      (z.im : ℂ) * (L Complex.I : ℂ) := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  simp only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]

private theorem realLinear_rotation (L : ℂ →L[ℝ] ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    u * ((L u : ℂ) + Complex.I * (L (Complex.I * u) : ℂ)) =
      (L (1 : ℂ) : ℂ) + Complex.I * (L Complex.I : ℂ) := by
  have hs : u.re ^ 2 + u.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two, hu] using
      (Complex.normSq_eq_norm_sq u)
  calc
    _ = ((u.re ^ 2 + u.im ^ 2 : ℝ) : ℂ) *
        ((L (1 : ℂ) : ℂ) + Complex.I * (L Complex.I : ℂ)) := by
      rw [realLinear_apply_complex L u, realLinear_apply_complex L (Complex.I * u)]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, zero_add, add_zero, one_mul, sub_zero, zero_sub]
      · ring
      · ring
    _ = _ := by rw [hs, Complex.ofReal_one, one_mul]

private theorem polar_kernel_identity (φ : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r • (((Real.pi : ℂ) * circleMap 0 r θ)⁻¹ * realTestDbar φ (circleMap 0 r θ)) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ((radialTest φ r θ : ℂ) + Complex.I * (angularTest φ r θ : ℂ)) := by
  have hu : ‖circleMap 0 1 θ‖ = 1 := by simp only [norm_circleMap_zero, abs_one]
  have hrot := realLinear_rotation (fderiv ℝ φ (circleMap 0 r θ)) hu
  have hur : circleMap 0 1 θ ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : ((Real.pi : ℂ) * circleMap 0 r θ)⁻¹ =
      ((Real.pi : ℂ) * ((r : ℂ) * circleMap 0 1 θ))⁻¹ := by
    rw [circleMap_eq_smul_unit r θ, Complex.real_smul]
  unfold realTestDbar radialTest angularTest
  rw [← hrot, hden]
  simp only [Complex.real_smul]
  field_simp [hr', hpi, hur]

private theorem integral_kernel_realTestDbar_zero {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ z : ℂ, ((Real.pi : ℂ) * z)⁻¹ * realTestDbar φ z) = -(φ 0 : ℂ) := by
  obtain ⟨R, hR, hs⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hout (z : ℂ) (hz : R ≤ ‖z‖) : z ∉ tsupport φ := by
    intro hm
    have hlt : ‖z‖ < R := by simpa only [mem_ball_zero_iff] using hs hm
    exact (not_lt_of_ge hz) hlt
  have hi : Integrable (fun z : ℂ => ((Real.pi : ℂ) * z)⁻¹ * realTestDbar φ z) := by
    simpa only [sub_zero] using integrable_kernel_realTestDbar hφ hc 0
  have hball : (∫ z : ℂ, ((Real.pi : ℂ) * z)⁻¹ * realTestDbar φ z) =
      ∫ z in ball (0 : ℂ) R, ((Real.pi : ℂ) * z)⁻¹ * realTestDbar φ z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hnot := hout z (le_of_not_gt (by simpa only [mem_ball_zero_iff] using hz))
    simp only [realTestDbar, fderiv_of_notMem_tsupport ℝ hnot, _root_.zero_apply,
      Complex.ofReal_zero, mul_zero, add_zero, zero_div]
  have hP := continuous_radialTest hφ
  have hQ := continuous_angularTest hφ
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hradial (θ : ℝ) : (∫ r in (0 : ℝ)..R, radialTest φ r θ) = -φ 0 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hasDerivAt_radialTest hφ r θ)
      ((hP.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 R)
    have hz : circleMap 0 R θ ∉ tsupport φ :=
      hout _ (by rw [norm_circleMap_zero, abs_of_pos hR])
    rw [image_eq_zero_of_notMem_tsupport hz] at hh
    simpa only [circleMap, Complex.ofReal_zero,
      zero_mul, zero_add, zero_sub] using hh
  have hswap :
      (∫ r in Ioo (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, radialTest φ r θ) =
        ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in Ioo (0 : ℝ) R, radialTest φ r θ := by
    simp_rw [integral_Ioo_eq_interval hR.le, integral_Ioo_eq_interval hpi]
    apply intervalIntegral_intervalIntegral_swap
    have hj := hP.continuousOn.integrableOn_compact (μ := (volume : Measure (ℝ × ℝ)))
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi))
    apply hj.mono_set
    simp only [uIoc_of_le hR.le, uIoc_of_le hpi]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hdouble :
      (∫ r in Ioo (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, radialTest φ r θ) =
        -(2 * Real.pi) * φ 0 := by
    rw [hswap]
    simp_rw [integral_Ioo_eq_interval hR.le, hradial]
    rw [integral_Ioo_eq_interval hpi, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hcircle (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      r • (∫ θ in Ioo (-Real.pi) Real.pi,
        ((Real.pi : ℂ) * circleMap 0 r θ)⁻¹ * realTestDbar φ (circleMap 0 r θ)) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ((∫ θ in Ioo (-Real.pi) Real.pi, radialTest φ r θ : ℝ) : ℂ) := by
    rw [← integral_smul]
    simp_rw [polar_kernel_identity φ hr.1]
    rw [integral_const_mul]
    have hiP : IntegrableOn (fun θ : ℝ => (radialTest φ r θ : ℂ))
        (Icc (-Real.pi) Real.pi) volume :=
      (Complex.continuous_ofReal.comp
        (hP.comp (continuous_const.prodMk continuous_id))).integrableOn_Icc
    have hiQ : IntegrableOn (fun θ : ℝ => Complex.I * (angularTest φ r θ : ℂ))
        (Icc (-Real.pi) Real.pi) volume :=
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (hQ.comp (continuous_const.prodMk continuous_id)))).integrableOn_Icc
    rw [integral_add (hiP.mono_set Ioo_subset_Icc_self)
      (hiQ.mono_set Ioo_subset_Icc_self), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal,
      integral_angularTest_eq_zero hφ hr.1, Complex.ofReal_zero, mul_zero, add_zero]
  rw [hball, integral_ball_zero_eq_integral_circle hi.integrableOn]
  rw [setIntegral_congr_fun measurableSet_Ioo hcircle, integral_const_mul,
    integral_complex_ofReal, hdouble]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The translated Cauchy kernel tested against the genuine real-test
Wirtinger derivative is integrable and has value minus the test at the pole.
This is the weak fundamental-solution identity for `∂bar = (∂x + i∂y)/2`;
no distributional equation or differentiability of a Cauchy integral is assumed. -/
theorem integrable_and_integral_cauchyKernel_mul_realTestDbar
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (w : ℂ) :
    Integrable (fun z : ℂ => ((Real.pi : ℂ) * (z - w))⁻¹ *
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2)) ∧
    (∫ z : ℂ, ((Real.pi : ℂ) * (z - w))⁻¹ *
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2)) =
        -(φ w : ℂ) := by
  refine ⟨integrable_kernel_realTestDbar hφ hc w, ?_⟩
  let ψ : ℂ → ℝ := fun z => φ (z + w)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.addRight w)
  have h := integral_kernel_realTestDbar_zero hψ hcψ
  have hd (z : ℂ) : realTestDbar ψ z = realTestDbar φ (z + w) := by
    simp only [realTestDbar, ψ, fderiv_comp_add_right]
  rw [show ψ 0 = φ w by simp only [ψ, zero_add]] at h
  change (∫ z : ℂ, ((Real.pi : ℂ) * (z - w))⁻¹ * realTestDbar φ z) = _
  rw [← integral_add_right_eq_self
    (fun z : ℂ => ((Real.pi : ℂ) * (z - w))⁻¹ * realTestDbar φ z) w]
  simpa only [add_sub_cancel_right, hd] using h

end DifferentialGeometry.Analysis
