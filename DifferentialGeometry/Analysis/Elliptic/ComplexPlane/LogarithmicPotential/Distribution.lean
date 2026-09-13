import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.FundamentalSolution
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence







noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis


theorem continuous_laplacian_complex {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have he : Laplacian.laplacian f = fun z => fderiv ℝ (fderiv ℝ f) z 1 1 +
      fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I :=
    funext (laplacian_complex_eq_fderiv f)
  rw [he]
  have h := (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  exact ((h.clm_apply continuous_const).clm_apply continuous_const).add
    ((h.clm_apply continuous_const).clm_apply continuous_const)


theorem integrable_log_norm_mul_laplacian {f : ℂ → ℝ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) :
    Integrable (fun z => Real.log ‖z‖ * Laplacian.laplacian f z) := by
  exact locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
    (continuous_laplacian_complex hf)
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f))

private theorem continuous_angular_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} (hf : Continuous f) :
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


theorem tendsto_polar_circle_integral_zero {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun r : ℝ => ∫ θ in -Real.pi..Real.pi, f (Complex.polarCoord.symm (r, θ)))
      (𝓝 0) (𝓝 ((2 * Real.pi) * f 0)) := by
  have hcont : Continuous (fun p : ℝ × ℝ => f (Complex.polarCoord.symm p)) := by
    apply hf.comp
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm
  have h := (continuous_angular_integral hcont).tendsto 0
  simpa [two_mul] using h



theorem tendsto_log_polar_test_derivative_zero {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Tendsto (fun r : ℝ => r * Real.log r *
      ∫ θ in -Real.pi..Real.pi,
        fderiv ℝ f (Complex.polarCoord.symm (r, θ))
          (Complex.polarCoord.symm (1, θ))) (𝓝 0) (𝓝 0) := by
  have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hunit : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm (1, p.2)) :=
    hp.comp (continuous_const.prodMk continuous_snd)
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hjoint := (hdf.comp hp).clm_apply hunit
  have hlim := (continuous_angular_integral hjoint).tendsto 0
  simpa only [zero_mul, Function.comp_apply] using! tendsto_self_mul_log_nhds_zero.mul hlim



theorem tendsto_integral_annulus_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → E} {R : ℝ}
    (hf : IntegrableOn f {z : ℂ | ‖z‖ ≤ R}) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z)
      (𝓝 0) (𝓝 (∫ z in {z : ℂ | ‖z‖ ≤ R}, f z)) := by
  let μ := volume.restrict {z : ℂ | ‖z‖ ≤ R}
  let A (r : ℝ) : Set ℂ := {z | r ≤ ‖z‖}
  have hm (r : ℝ) : MeasurableSet (A r) := measurableSet_le measurable_const measurable_norm
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun r : ℝ => (A r).indicator f z) (𝓝 0) (𝓝 (f z)) := by
    have hz : ∀ᵐ z : ℂ ∂μ, z ≠ 0 := by
      apply ae_restrict_of_ae
      simp [ae_iff]
    filter_upwards [hz] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_nhds (norm_pos_iff.mpr hz)] with r hr
    exact (indicator_of_mem (show z ∈ A r from hr.le) f).symm
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun z => ‖f z‖)
    (Eventually.of_forall fun r => hf.aestronglyMeasurable.indicator (hm r))
    (Eventually.of_forall fun r => Eventually.of_forall fun z => norm_indicator_le_norm_self f z)
    hf.norm hlim
  have he (r : ℝ) : (∫ z, (A r).indicator f z ∂μ) =
      ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z := by
    rw [show μ = volume.restrict {z : ℂ | ‖z‖ ≤ R} from rfl, setIntegral_indicator (hm r)]
    have hs : {z : ℂ | ‖z‖ ≤ R} ∩ A r = {z : ℂ | ‖z‖ ∈ Icc r R} := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, A, mem_Icc, and_comm]
    rw [hs]
  simpa only [he] using h


theorem polar_point_eq_smul_unit (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = r • Complex.polarCoord.symm (1, θ) := by
  simp [Complex.polarCoord_symm_apply, Complex.real_smul, mul_add]



theorem fderiv_log_norm_polar_unit {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    fderiv ℝ (fun z : ℂ => Real.log ‖z‖) (Complex.polarCoord.symm (r, θ))
      (Complex.polarCoord.symm (1, θ)) = r⁻¹ := by
  have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
  have hz : Complex.polarCoord.symm (r, θ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact hr.ne'
  rw [(hasFDerivAt_log_norm_complex hz).fderiv]
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
    polar_point_eq_smul_unit r θ, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Complex.norm_polarCoord_symm, abs_one, one_pow, mul_one, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr]
  field_simp [hr.ne']


theorem greenRadialFlux_log (f : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f r θ =
      r * Real.log r * fderiv ℝ f (Complex.polarCoord.symm (r, θ))
        (Complex.polarCoord.symm (1, θ)) - f (Complex.polarCoord.symm (r, θ)) := by
  simp only [greenRadialFlux, Complex.norm_polarCoord_symm, abs_of_pos hr,
    fderiv_log_norm_polar_unit hr]
  field_simp


theorem integral_log_laplacian_annulus {f : ℂ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hf : ∀ z, ‖z‖ ∈ Icc r R → ContDiffAt ℝ 2 f z) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, Real.log ‖z‖ * Laplacian.laplacian f z) =
      (∫ θ in -Real.pi..Real.pi, greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f R θ) -
        ∫ θ in -Real.pi..Real.pi, greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f r θ := by
  have hz (z : ℂ) (h : ‖z‖ ∈ Icc r R) : z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le h.1))
  have hlog z h : ContDiffAt ℝ 2 (fun z : ℂ => Real.log ‖z‖) z :=
    (contDiffAt_id.norm ℝ (hz z h)).log (norm_ne_zero_iff.mpr (hz z h))
  rw [← integral_green_annulus hr hrR hlog hf]
  apply setIntegral_congr_fun (measurableSet_Icc.preimage continuous_norm.measurable)
  intro z h
  simp only [laplacian_log_norm_complex (hz z h), mul_zero, sub_zero]



theorem tendsto_integral_greenRadialFlux_log_zero {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Tendsto (fun r : ℝ => ∫ θ in -Real.pi..Real.pi,
      greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f r θ)
      (𝓝[>] 0) (𝓝 (-((2 * Real.pi) * f 0))) := by
  have h := (tendsto_log_polar_test_derivative_zero hf).sub
    (tendsto_polar_circle_integral_zero hf.continuous)
  simp only [zero_sub] at h
  apply (h.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have he : Continuous (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hd := ((hf.continuous_fderiv (by norm_num)).comp hp).clm_apply he
  simp_rw [greenRadialFlux_log f hr]
  erw [intervalIntegral.integral_sub
    ((continuous_const.mul hd).intervalIntegrable _ _)
    ((hf.continuous.comp hp).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  rfl




theorem integral_log_norm_mul_laplacian {f : ℂ → ℝ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) :
    (∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian f z) = (2 * Real.pi) * f 0 := by
  obtain ⟨R, hR, hs⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hout (z : ℂ) (hz : R ≤ ‖z‖) : z ∉ tsupport f := by
    intro h
    have hlt : ‖z‖ < R := by simpa only [mem_ball_zero_iff] using hs h
    exact (not_lt_of_ge hz) hlt
  have hedge (θ : ℝ) : greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f R θ = 0 := by
    have hz : Complex.polarCoord.symm (R, θ) ∉ tsupport f :=
      hout _ (by rw [Complex.norm_polarCoord_symm, abs_of_pos hR])
    simp only [greenRadialFlux]
    rw [fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
    simp
  have hi := integrable_log_norm_mul_laplacian hc hf
  have heq : (∫ z in {z : ℂ | ‖z‖ ≤ R}, Real.log ‖z‖ * Laplacian.laplacian f z) =
      ∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport (Laplacian.laplacian f) :=
      fun h => hout z (le_of_not_ge hz) (tsupport_laplacian_subset f h)
    rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hlim := (tendsto_integral_annulus_zero (R := R) hi.integrableOn).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  rw [heq] at hlim
  have hflux := (tendsto_integral_greenRadialFlux_log_zero hf).neg
  simp only [neg_neg] at hflux
  have hgreen : Tendsto (fun r : ℝ => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      Real.log ‖z‖ * Laplacian.laplacian f z) (𝓝[>] 0) (𝓝 ((2 * Real.pi) * f 0)) := by
    apply hflux.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono inf_le_left] with r hr hrR
    rw [integral_log_laplacian_annulus hr hrR.le (fun z _ => hf.contDiffAt)]
    simp only [hedge, intervalIntegral.integral_zero, zero_sub]
  exact tendsto_nhds_unique hlim hgreen

end DifferentialGeometry.Analysis
