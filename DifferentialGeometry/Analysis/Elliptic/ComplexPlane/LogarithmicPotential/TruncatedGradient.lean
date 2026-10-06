import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.Distribution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff Interval RealInnerProductSpace

namespace DifferentialGeometry.Analysis

private def logGradient (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (‖z‖ ^ 2)⁻¹ • innerSL ℝ z

private theorem norm_logGradient (z : ℂ) : ‖logGradient z‖ = ‖z‖⁻¹ := by
  rw [logGradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), innerSL_apply_norm]
  by_cases hz : z = 0
  · simp [hz]
  · field_simp [norm_ne_zero_iff.mpr hz]

private theorem locallyIntegrable_logGradient :
    LocallyIntegrable logGradient (volume : Measure ℂ) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex])
  · exact Eventually.of_forall fun z => by
      simp only [norm_logGradient, Real.rpow_neg_one, one_mul, le_refl]
  · exact (((continuous_norm.pow 2).measurable.inv).stronglyMeasurable.smul
      (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).continuous.stronglyMeasurable).aestronglyMeasurable

private theorem locallyIntegrable_logGradient_apply (v : ℂ) :
    LocallyIntegrable (fun z => logGradient z v) (volume : Measure ℂ) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp
    (locallyIntegrable_logGradient.integrableOn_isCompact hK)

private theorem realLinear_apply (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = v.re * L 1 + v.im * L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  conv_lhs => rw [hv, map_add, map_smul, map_smul]
  rfl

private theorem continuous_angular_integral {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) :
    Continuous (fun r : ℝ => ∫ θ in -Real.pi..Real.pi, f (r, θ)) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (f := fun r θ => f (r, θ)) (by convert! hf)
    (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi))
  have he (r : ℝ) : (∫ θ in -Real.pi..Real.pi, f (r, θ)) =
      ∫ θ in Icc (-Real.pi) Real.pi, f (r, θ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))
  simp_rw [he]
  exact h

/-- The puncture error has the genuine `ε |log ε|` vanishing factor. -/
theorem tendsto_abs_mul_abs_log_zero :
    Tendsto (fun r : ℝ => |r| * |Real.log r|) (𝓝 0) (𝓝 0) := by
  simpa only [abs_mul, abs_zero] using tendsto_self_mul_log_nhds_zero.abs

private theorem tendsto_log_flux_zero {ψ : ℂ → ℝ} (hψ : Continuous ψ) (v : ℂ) :
    Tendsto (fun r : ℝ => ∫ θ in -Real.pi..Real.pi,
      (r * Real.log r) * ψ (Complex.polarCoord.symm (r, θ)) *
        (v.re * Real.cos θ + v.im * Real.sin θ)) (𝓝 0) (𝓝 0) := by
  let A (r : ℝ) := ∫ θ in -Real.pi..Real.pi,
    ψ (Complex.polarCoord.symm (r, θ)) *
      (v.re * Real.cos θ + v.im * Real.sin θ)
  have hA : Continuous A := by
    have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact continuous_angular_integral
      (f := fun p : ℝ × ℝ => ψ (Complex.polarCoord.symm p) *
        (v.re * Real.cos p.2 + v.im * Real.sin p.2))
      ((hψ.comp hp).mul (by fun_prop))
  have h := tendsto_self_mul_log_nhds_zero.mul (hA.tendsto 0)
  simp only [zero_mul] at h
  apply h.congr'
  exact Eventually.of_forall fun r => by
    dsimp only [A]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext θ
    ring

private theorem divergence_log_test {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (v : ℂ) {z : ℂ} (hz : z ≠ 0) :
    complexDivergence
      (fun q => (ψ q * Real.log ‖q‖) * v.re)
      (fun q => (ψ q * Real.log ‖q‖) * v.im) z =
      Real.log ‖z‖ * fderiv ℝ ψ z v + ψ z * logGradient z v := by
  have hdψ := hψ.differentiable (by norm_num) z
  have hdlog := (hasFDerivAt_log_norm_complex hz).differentiableAt
  have hdprod : DifferentiableAt ℝ (fun q : ℂ => ψ q * Real.log ‖q‖) z :=
    hdψ.mul hdlog
  unfold complexDivergence
  rw [fderiv_mul_const hdprod, fderiv_mul_const hdprod,
    fderiv_fun_mul hdψ hdlog, (hasFDerivAt_log_norm_complex hz).fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul]
  rw [realLinear_apply (fderiv ℝ ψ z) v, realLinear_apply (logGradient z) v]
  dsimp only [logGradient]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

private theorem integral_log_directional_test {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (v : ℂ) :
    (∫ z : ℂ, Real.log ‖z‖ * fderiv ℝ ψ z v) =
      -(∫ z : ℂ, ψ z * logGradient z v) := by
  have hi₁ : Integrable (fun z : ℂ => Real.log ‖z‖ * fderiv ℝ ψ z v) :=
    locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
      ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (hcψ.fderiv_apply ℝ v)
  have hi₂ : Integrable (fun z : ℂ => ψ z * logGradient z v) :=
    (locallyIntegrable_logGradient_apply v).integrable_smul_left_of_hasCompactSupport
      hψ.continuous hcψ
  let f (z : ℂ) := Real.log ‖z‖ * fderiv ℝ ψ z v + ψ z * logGradient z v
  have hi : Integrable f := hi₁.add hi₂
  obtain ⟨R, hR, hs⟩ := hcψ.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hout (z : ℂ) (hz : R ≤ ‖z‖) : z ∉ tsupport ψ := by
    intro hm
    have hlt : ‖z‖ < R := by simpa only [mem_ball_zero_iff] using hs hm
    exact (not_lt_of_ge hz) hlt
  have heq : (∫ z in {z : ℂ | ‖z‖ ≤ R}, f z) = ∫ z : ℂ, f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn := hout z (le_of_not_ge hz)
    simp only [f, fderiv_of_notMem_tsupport ℝ hn,
      image_eq_zero_of_notMem_tsupport hn, _root_.zero_apply, mul_zero, zero_mul, add_zero]
  have hlim := (tendsto_integral_annulus_zero (R := R) hi.integrableOn).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  rw [heq] at hlim
  have hann {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z) =
        -(∫ θ in -Real.pi..Real.pi,
          (r * Real.log r) * ψ (Complex.polarCoord.symm (r, θ)) *
            (v.re * Real.cos θ + v.im * Real.sin θ)) := by
    have hlog (z : ℂ) (hz : ‖z‖ ∈ Icc r R) :
        ContDiffAt ℝ 1 (fun q : ℂ => Real.log ‖q‖) z := by
      have hn : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hz.1))
      exact ((contDiffAt_id.norm ℝ hn).log (norm_ne_zero_iff.mpr hn))
    have hd := integral_complexDivergence_annulus
      (F := fun q => (ψ q * Real.log ‖q‖) * v.re)
      (G := fun q => (ψ q * Real.log ‖q‖) * v.im) hr hrR
      (fun z hz => ((hψ.contDiffAt.mul (hlog z hz)).mul contDiffAt_const))
      (fun z hz => ((hψ.contDiffAt.mul (hlog z hz)).mul contDiffAt_const))
    have hleft : (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z) =
        ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, complexDivergence
          (fun q => (ψ q * Real.log ‖q‖) * v.re)
          (fun q => (ψ q * Real.log ‖q‖) * v.im) z := by
      apply setIntegral_congr_fun (measurableSet_Icc.preimage measurable_norm)
      intro z hz
      exact (divergence_log_test hψ v
        (norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hz.1)))).symm
    rw [hleft, hd]
    have hedge (θ : ℝ) : ψ (Complex.polarCoord.symm (R, θ)) = 0 :=
      image_eq_zero_of_notMem_tsupport (hout _
        (by rw [Complex.norm_polarCoord_symm, abs_of_pos hR]))
    simp only [hedge, zero_mul, zero_add, mul_zero, intervalIntegral.integral_zero, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    ring
  have hflux := ((tendsto_log_flux_zero hψ.continuous v).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)).neg
  simp only [neg_zero] at hflux
  have hzero : Tendsto (fun r : ℝ => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z)
      (𝓝[>] 0) (𝓝 0) := by
    apply hflux.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono inf_le_left] with r hr hrR
    exact (hann hr hrR.le).symm
  have h := tendsto_nhds_unique hlim hzero
  rw [show (∫ z : ℂ, f z) = (∫ z : ℂ, Real.log ‖z‖ * fderiv ℝ ψ z v) +
    (∫ z : ℂ, ψ z * logGradient z v) from integral_add hi₁ hi₂] at h
  linarith

/-- The literal compactly truncated, negatively normalized logarithmic kernel. -/
def truncatedLogKernel (χ : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * (χ z * Real.log ‖z‖)

/-- The actual product-rule differential, totalized at the null pole. -/
def truncatedLogGradient (χ : ℂ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (-(2 * Real.pi)⁻¹) •
    (Real.log ‖z‖ • fderiv ℝ χ z + χ z • logGradient z)

theorem hasFDerivAt_truncatedLogKernel {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (truncatedLogKernel χ) (truncatedLogGradient χ z) z := by
  have h := (((hχ.differentiable (by norm_num) z).hasFDerivAt).mul
    (hasFDerivAt_log_norm_complex hz)).const_mul (-(2 * Real.pi)⁻¹)
  change HasFDerivAt (fun y : ℂ => -(2 * Real.pi)⁻¹ * (χ y * Real.log ‖y‖)) _ z
  simpa only [Pi.mul_apply, truncatedLogGradient, logGradient, add_comm] using h

theorem norm_truncatedLogGradient_le (χ : ℂ → ℝ) (z : ℂ) :
    ‖truncatedLogGradient χ z‖ ≤ (2 * Real.pi)⁻¹ *
      (|Real.log ‖z‖| * ‖fderiv ℝ χ z‖ + |χ z| * ‖z‖⁻¹) := by
  rw [truncatedLogGradient, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_logGradient])

theorem integrable_truncatedLogKernel {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) :
    Integrable (truncatedLogKernel χ) (volume : Measure ℂ) := by
  exact (locallyIntegrable_log_norm_complex.integrable_smul_left_of_hasCompactSupport
    hχ.continuous hcχ).const_mul _

theorem integrable_truncatedLogGradient {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) :
    Integrable (truncatedLogGradient χ) (volume : Measure ℂ) := by
  have h₁ := locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
    (hχ.continuous_fderiv (by norm_num)) (hcχ.fderiv ℝ)
  have h₂ := locallyIntegrable_logGradient.integrable_smul_left_of_hasCompactSupport
    hχ.continuous hcχ
  exact (h₁.add h₂).smul (-(2 * Real.pi)⁻¹ : ℝ)

theorem truncatedLogGradient_eq_near_zero {χ : ℂ → ℝ}
    (hχ : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ)) :
    truncatedLogGradient χ =ᶠ[𝓝 (0 : ℂ)]
      fun z => (-(2 * Real.pi)⁻¹) • ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) := by
  filter_upwards [hχ, hχ.fderiv (𝕜 := ℝ)] with z hz hdz
  rw [fderiv_const_apply] at hdz
  simp only [truncatedLogGradient, logGradient, hz, hdz,
    smul_zero, zero_add, one_smul]

theorem norm_truncatedLogGradient_eq_near_zero {χ : ℂ → ℝ}
    (hχ : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ)) :
    (fun z => ‖truncatedLogGradient χ z‖) =ᶠ[𝓝 (0 : ℂ)]
      fun z => (2 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  filter_upwards [truncatedLogGradient_eq_near_zero hχ] with z hz
  rw [hz]
  change ‖(-(2 * Real.pi)⁻¹) • logGradient z‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), norm_logGradient]

/-- Genuine integration by parts for the same logarithmic kernel and its full
L1 differential. The test is only C1; no weak derivative is supplied as data. -/
theorem integrable_and_integral_truncatedLogKernel_directional_test
    {χ φ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z : ℂ => truncatedLogKernel χ z * fderiv ℝ φ z v) ∧
    Integrable (fun z : ℂ => φ z * truncatedLogGradient χ z v) ∧
    (∫ z : ℂ, truncatedLogKernel χ z * fderiv ℝ φ z v) =
      -(∫ z : ℂ, φ z * truncatedLogGradient χ z v) := by
  let a (z : ℂ) := Real.log ‖z‖ * (χ z * fderiv ℝ φ z v)
  let b (z : ℂ) := Real.log ‖z‖ * (φ z * fderiv ℝ χ z v)
  let c (z : ℂ) := (χ z * φ z) * logGradient z v
  have ha : Integrable a :=
    locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      hcχ.mul_right
  have hb : Integrable b :=
    locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
      (hφ.continuous.mul ((hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      hcφ.mul_right
  have hc : Integrable c :=
    (locallyIntegrable_logGradient_apply v).integrable_smul_left_of_hasCompactSupport
      (hχ.continuous.mul hφ.continuous) hcχ.mul_right
  have hweak := integral_log_directional_test (hχ.mul hφ) hcχ.mul_right v
  have hexp : (fun z : ℂ => Real.log ‖z‖ * fderiv ℝ (fun q => χ q * φ q) z v) =
      fun z => a z + b z := by
    funext z
    rw [fderiv_fun_mul (hχ.differentiable (by norm_num) z)
      (hφ.differentiable (by norm_num) z)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, a, b]
    ring
  rw [hexp, integral_add ha hb] at hweak
  have he₁ : (fun z : ℂ => truncatedLogKernel χ z * fderiv ℝ φ z v) =
      fun z => -(2 * Real.pi)⁻¹ * a z := by
    funext z
    dsimp [truncatedLogKernel, a]
    ring
  have he₂ : (fun z : ℂ => φ z * truncatedLogGradient χ z v) =
      fun z => -(2 * Real.pi)⁻¹ * (b z + c z) := by
    funext z
    simp only [truncatedLogGradient, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul, b, c]
    ring
  rw [he₁, he₂]
  refine ⟨ha.const_mul _, (hb.add hc).const_mul _, ?_⟩
  rw [integral_const_mul, integral_const_mul, integral_add hb hc]
  change (∫ z, a z) + (∫ z, b z) = -(∫ z, c z) at hweak
  linear_combination (-(2 * Real.pi)⁻¹) * hweak

end DifferentialGeometry.Analysis
