import DifferentialGeometry.Analysis.Convex.Convolution
import DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import DifferentialGeometry.Analysis.Integration.Integral.Convergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Convolution

theorem ConvexOn.integral_hessian_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (v : E) :
    Integrable (fun x => B x v v * φ x) μ ∧
      (∫ x, B x v v * φ x ∂μ) ≤ ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v v ∂μ := by
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  let χ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let κ := χ.normed μ
  have hκd : ContDiff ℝ 2 κ := χ.contDiff_normed
  have hκc : HasCompactSupport κ := χ.hasCompactSupport_normed
  have hκ0 : ∀ x, 0 ≤ κ x := χ.nonneg_normed
  have hκm : ∫ x, κ x ∂μ = 1 := χ.integral_normed
  let k : ℝ → E → ℝ := fun r z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)
  let g : ℝ → E → ℝ := fun r => k r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u
  have hkd (r : ℝ) : ContDiff ℝ 2 (k r) :=
    contDiff_const.mul (hκd.comp (contDiff_const.smul contDiff_id))
  have hkc {r : ℝ} (hr : 0 < r) : HasCompactSupport (k r) := by
    have h : HasCompactSupport (fun z : E => κ (r⁻¹ • z)) :=
      hκc.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr.ne')).unit)
    exact h.mul_left
  have hkm {r : ℝ} (hr : 0 < r) : ∫ x, k r x ∂μ = 1 := by
    dsimp only [k]
    rw [integral_const_mul, μ.integral_comp_inv_smul_of_nonneg κ hr.le, hκm]
    simp only [smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]
  have hg {r : ℝ} (hr : 0 < r) : ContDiff ℝ 2 (g r) :=
    (hkc hr).contDiff_convolution_left _ (hkd r) huc.locallyIntegrable
  have hlow {r : ℝ} (hr : 0 < r) (x : E) :
      -A v v ≤ fderiv ℝ (fderiv ℝ (g r)) x v v := by
    have hk0 : ∀ᵐ z ∂μ, 0 ≤ k r z := ae_of_all μ fun z =>
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (hκ0 _)
    have h := hu.fderiv_fderiv_convolution_left_lower_bound A hA hk0
      ((hkd r).continuous.integrable_of_hasCompactSupport (hkc hr))
      (hkd r) (hkc hr) huc.locallyIntegrable x v
    simpa only [hkm hr, neg_one_mul] using h
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hr⟩
  let K : E → ℝ := fun x => fderiv ℝ (fderiv ℝ φ) x v v
  have hK : Continuous K :=
    (((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hKc : HasCompactSupport K :=
    ((hφc.fderiv ℝ).fderiv_apply ℝ v).comp_left (g := fun D : E →L[ℝ] ℝ => D v) rfl
  have huni := DifferentialGeometry.Analysis.tendstoLocallyUniformly_convolution_rescale
    (μ := μ) hκ0 (hκc.isCompact.isBounded.subset (subset_tsupport κ)) hκm huc
  have hKuni : TendstoUniformlyOn g u (𝓝[>] (0 : ℝ)) (Function.support K) :=
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKc.isCompact).mp
      huni.tendstoLocallyUniformlyOn).mono (subset_tsupport K)
  have hgi : ∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable (fun x => K x • g t x) μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hK.smul (hg ht).continuous).integrable_of_hasCompactSupport hKc.smul_right
  have hui : Integrable (fun x => K x • u x) μ :=
    (hK.smul huc).integrable_of_hasCompactSupport hKc.smul_right
  have hI := hKuni.integral_smul (hK.integrable_of_hasCompactSupport hKc) hgi hui
  have hIBP (n : ℕ) : (∫ x, fderiv ℝ (fderiv ℝ (g (r n))) x v v * φ x ∂μ) =
      ∫ x, g (r n) x * K x ∂μ := by
    have h := DifferentialGeometry.Analysis.integral_fderiv_fderiv_mul_eq_of_locallyLipschitzOn_fderiv
      (μ := μ) isOpen_univ ((hg (hr n)).differentiable (by norm_num)).differentiableOn
      ((hg (hr n)).fderiv_right (m := 1) (by norm_num)).locallyLipschitz.locallyLipschitzOn
      hφ hφc (subset_univ _) v v
    simpa only [Measure.restrict_univ] using h
  have hint : Tendsto (fun n => ∫ x, fderiv ℝ (fderiv ℝ (g (r n))) x v v * φ x ∂μ)
      atTop (𝓝 (∫ x, u x * K x ∂μ)) := by
    simp_rw [hIBP]
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hI.comp hrt
  have hFi (n : ℕ) : Integrable (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x v v * φ x) μ := by
    have hc : Continuous (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x v v) :=
      ((((hg (hr n)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).clm_apply continuous_const
    exact (hc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hlower : Integrable (fun x => -A v v * φ x) μ :=
    (hφ.continuous.integrable_of_hasCompactSupport hφc).const_mul _
  have hbound (n : ℕ) : (fun x => -A v v * φ x) ≤ᵐ[μ]
      (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x v v * φ x) :=
    ae_of_all μ fun x => mul_le_mul_of_nonneg_right (hlow (hr n) x) (hφ0 x)
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n => fderiv ℝ (fderiv ℝ (g (r n))) x v v * φ x)
      atTop (𝓝 (B x v v * φ x)) := by
    filter_upwards [hB] with x hx
    obtain ⟨hsym, p, hp⟩ := hx
    have ht := DifferentialGeometry.Analysis.tendsto_fderiv_fderiv_convolution_rescale_of_isLittleO
      hκd hκc hκm huc.locallyIntegrable hsym hp
    have heval : Continuous (fun D : E →L[ℝ] E →L[ℝ] ℝ => D v v) := by fun_prop
    exact ((heval.tendsto (B x)).comp (ht.comp hrt)).mul_const _
  exact MeasureTheory.integrable_and_integral_le_of_tendsto_ae hFi hlower hbound hlim hint
