import DifferentialGeometry.Analysis.Integration.Integral.Laplacian
import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace DifferentialGeometry.Analysis

private def boundaryCutoff (ε : ℝ) (z : ℂ) : ℝ :=
  1 - CutoffProfile.value (z.im / ε)

private theorem contDiff_boundaryCutoff (ε : ℝ) : ContDiff ℝ ∞ (boundaryCutoff ε) := by
  exact contDiff_const.sub (CutoffProfile.contDiff.comp (Complex.imCLM.contDiff.div_const ε))

private theorem hasFDerivAt_comp_im_div {φ : ℝ → ℝ} {ε : ℝ} {z : ℂ}
    (hφ : DifferentiableAt ℝ φ (z.im / ε)) :
    HasFDerivAt (fun w : ℂ => φ (w.im / ε))
      ((deriv φ (z.im / ε) / ε) • Complex.imCLM) z := by
  have hlin : HasFDerivAt (fun w : ℂ => w.im / ε) (ε⁻¹ • Complex.imCLM) z := by
    have h := (Complex.imCLM.hasFDerivAt (x := z)).const_smul ε⁻¹
    change HasFDerivAt (fun w : ℂ => ε⁻¹ * w.im) (ε⁻¹ • Complex.imCLM) z at h
    simpa only [div_eq_mul_inv, mul_comm] using! h
  have h := hφ.hasDerivAt.comp_hasFDerivAt z hlin
  simpa only [Function.comp_apply, smul_smul, div_eq_mul_inv] using! h

private theorem boundaryCutoff_fderiv (ε : ℝ) (z : ℂ) :
    fderiv ℝ (boundaryCutoff ε) z =
      (-deriv CutoffProfile.value (z.im / ε) / ε) • Complex.imCLM := by
  have h := (hasFDerivAt_comp_im_div
    (CutoffProfile.contDiff.differentiable (by simp) (z.im / ε))).const_sub 1
  change fderiv ℝ (fun w : ℂ => 1 - CutoffProfile.value (w.im / ε)) z = _
  erw [h.fderiv]
  ext w
  simp only [_root_.neg_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem boundaryCutoff_laplacian (ε : ℝ) (z : ℂ) :
    Laplacian.laplacian (boundaryCutoff ε) z =
      -deriv (deriv CutoffProfile.value) (z.im / ε) / ε ^ 2 := by
  have hd : DifferentiableAt ℝ (deriv CutoffProfile.value) (z.im / ε) :=
    ((show ContDiff ℝ 2 CutoffProfile.value from
      CutoffProfile.contDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).deriv' (n := 1)).differentiable (by norm_num) _
  have h := ((hasFDerivAt_comp_im_div hd).neg.mul_const ε⁻¹).smul_const Complex.imCLM
  have he : fderiv ℝ (boundaryCutoff ε) =
      fun w => (-deriv CutoffProfile.value (w.im / ε) * ε⁻¹) • Complex.imCLM := by
    funext w
    rw [boundaryCutoff_fderiv, div_eq_mul_inv]
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, he]
  erw [h.fderiv]
  simp [div_eq_mul_inv]
  ring

private theorem boundaryCutoff_mem_Icc (ε : ℝ) (z : ℂ) :
    boundaryCutoff ε z ∈ Icc (0 : ℝ) 1 := by
  have h := CutoffProfile.mem_Icc (z.im / ε)
  dsimp [boundaryCutoff]
  constructor <;> linarith [h.1, h.2]

private theorem boundaryCutoff_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : z.im ≤ ε) :
    boundaryCutoff ε z = 0 := by
  rw [boundaryCutoff, CutoffProfile.one_of_le_one ((div_le_one hε).mpr hz), sub_self]

private theorem boundaryCutoff_one {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 2 * ε ≤ z.im) :
    boundaryCutoff ε z = 1 := by
  rw [boundaryCutoff, CutoffProfile.zero_of_two_le ((le_div_iff₀ hε).mpr hz), sub_zero]

private theorem boundaryCutoff_norm_fderiv_le {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖fderiv ℝ (boundaryCutoff ε) z‖ ≤ CutoffProfile.derivBound / ε := by
  have him : ‖Complex.imCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm w
  rw [boundaryCutoff_fderiv, norm_smul]
  simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hε]
  calc
    |deriv CutoffProfile.value (z.im / ε)| / ε * ‖Complex.imCLM‖ ≤
        (CutoffProfile.derivBound / ε) * 1 := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (CutoffProfile.abs_deriv_le_derivBound _) hε.le
      · exact him
      · exact norm_nonneg _
      · exact div_nonneg CutoffProfile.derivBound_nonneg hε.le
    _ = _ := mul_one _

private theorem boundaryCutoff_im_mul_norm_fderiv_le {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) :
    z.im * ‖fderiv ℝ (boundaryCutoff ε) z‖ ≤ 2 * CutoffProfile.derivBound := by
  have hC := CutoffProfile.derivBound_nonneg
  by_cases hsmall : z.im ≤ 2 * ε
  · calc
      z.im * ‖fderiv ℝ (boundaryCutoff ε) z‖ ≤
          (2 * ε) * (CutoffProfile.derivBound / ε) :=
        mul_le_mul hsmall (boundaryCutoff_norm_fderiv_le hε z) (norm_nonneg _) (by positivity)
      _ = 2 * CutoffProfile.derivBound := by field_simp
  · have hd := CutoffProfile.deriv_zero_of_ge ((le_div_iff₀ hε).mpr (le_of_not_ge hsmall))
    rw [boundaryCutoff_fderiv, hd]
    simp only [neg_zero, zero_div, zero_smul, ContinuousLinearMap.opNorm_zero, mul_zero]
    positivity

private theorem boundaryCutoff_im_sq_mul_abs_laplacian_le {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : 0 ≤ z.im) :
    z.im ^ 2 * |Laplacian.laplacian (boundaryCutoff ε) z| ≤
      4 * CutoffProfile.derivBound := by
  have hC := CutoffProfile.derivBound_nonneg
  rw [boundaryCutoff_laplacian]
  simp only [abs_div, abs_neg, abs_pow, abs_of_pos hε]
  by_cases hsmall : z.im ≤ 2 * ε
  · have hsq : z.im ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
    calc
      z.im ^ 2 * (|deriv (deriv CutoffProfile.value) (z.im / ε)| / ε ^ 2) ≤
          (4 * ε ^ 2) * (CutoffProfile.derivBound / ε ^ 2) :=
        mul_le_mul hsq
          (div_le_div_of_nonneg_right (CutoffProfile.abs_deriv2_le_derivBound _) (sq_nonneg ε))
          (by positivity) (by positivity)
      _ = 4 * CutoffProfile.derivBound := by field_simp
  · rw [CutoffProfile.deriv2_zero_of_ge ((le_div_iff₀ hε).mpr (le_of_not_ge hsmall))]
    simp only [abs_zero, zero_div, mul_zero]
    positivity

private theorem norm_le_mul_im_of_zero_on_real {φ : ℂ → ℝ} {D : ℝ}
    (hφ : Differentiable ℝ φ) (hD : ∀ z, ‖fderiv ℝ φ z‖ ≤ D)
    (hz : ∀ z : ℂ, z.im = 0 → φ z = 0) {z : ℂ} (hi : 0 ≤ z.im) :
    ‖φ z‖ ≤ D * z.im := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℂ)).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hφ w) (fun w _ => hD w) (x := (z.re : ℂ)) (y := z) (mem_univ _) (mem_univ _)
  have he : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hzre : φ (z.re : ℂ) = 0 := hz _ rfl
  rw [hzre, sub_zero, he, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg hi] using h

private theorem boundaryCutoff_error_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {ε D K : ℝ} {z : ℂ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hK : 0 ≤ K) (hi : 0 ≤ z.im)
    (hφ : ContDiffAt ℝ 2 φ z) (hφ0 : ‖φ z‖ ≤ D * z.im)
    (hφ1 : ‖fderiv ℝ φ z‖ ≤ D) (hf : ‖f z‖ ≤ K * z.im) :
    ‖(Laplacian.laplacian (fun w => boundaryCutoff ε w * φ w) z -
      boundaryCutoff ε z * Laplacian.laplacian φ z) • f z‖ ≤
        8 * CutoffProfile.derivBound * D * K := by
  have hc : ContDiffAt ℝ 2 (boundaryCutoff ε) z :=
    ((contDiff_boundaryCutoff ε).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).contDiffAt
  have hprod := hc.laplacian_fun_smul hφ
  simp only [smul_eq_mul] at hprod
  rw [hprod]
  have he : boundaryCutoff ε z * Laplacian.laplacian φ z +
      2 * fderiv ℝ φ z (gradient (boundaryCutoff ε) z) +
      Laplacian.laplacian (boundaryCutoff ε) z * φ z -
      boundaryCutoff ε z * Laplacian.laplacian φ z =
        2 * fderiv ℝ φ z (gradient (boundaryCutoff ε) z) +
          Laplacian.laplacian (boundaryCutoff ε) z * φ z := by ring
  rw [he, norm_smul]
  have hn : ‖fderiv ℝ φ z (gradient (boundaryCutoff ε) z)‖ ≤
      ‖fderiv ℝ (boundaryCutoff ε) z‖ * D := by
    have h := (fderiv ℝ φ z).le_opNorm (gradient (boundaryCutoff ε) z)
    simp only [gradient, LinearIsometryEquiv.norm_map] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hg := boundaryCutoff_im_mul_norm_fderiv_le hε z
  have hl := boundaryCutoff_im_sq_mul_abs_laplacian_le hε hi
  calc
    ‖2 * fderiv ℝ φ z (gradient (boundaryCutoff ε) z) +
        Laplacian.laplacian (boundaryCutoff ε) z * φ z‖ * ‖f z‖ ≤
      (2 * ‖fderiv ℝ (boundaryCutoff ε) z‖ * D +
        |Laplacian.laplacian (boundaryCutoff ε) z| * (D * z.im)) * (K * z.im) := by
      apply mul_le_mul _ hf (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (by
        simp only [norm_mul, Real.norm_ofNat, Real.norm_eq_abs]
        have hn' : |fderiv ℝ φ z (gradient (boundaryCutoff ε) z)| ≤
            ‖fderiv ℝ (boundaryCutoff ε) z‖ * D := hn
        have hp' : |φ z| ≤ D * z.im := hφ0
        calc
          _ ≤ 2 * (‖fderiv ℝ (boundaryCutoff ε) z‖ * D) +
              |Laplacian.laplacian (boundaryCutoff ε) z| * (D * z.im) :=
            add_le_add (mul_le_mul_of_nonneg_left hn' (by norm_num))
              (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
          _ = _ := by ring)
    _ = (2 * (z.im * ‖fderiv ℝ (boundaryCutoff ε) z‖) +
        z.im ^ 2 * |Laplacian.laplacian (boundaryCutoff ε) z|) * D * K := by ring
    _ ≤ (2 * (2 * CutoffProfile.derivBound) + 4 * CutoffProfile.derivBound) * D * K := by
      gcongr
    _ = 8 * CutoffProfile.derivBound * D * K := by ring

private theorem boundaryCutoff_tsupport_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (boundaryCutoff ε) ⊆ {z : ℂ | ε ≤ z.im} := by
  apply closure_minimal _ (isClosed_le continuous_const Complex.continuous_im)
  intro z hz
  by_contra hn
  change ¬ε ≤ z.im at hn
  exact hz (boundaryCutoff_zero hε (not_le.mp hn).le)

private theorem boundaryCutoff_eventually_one {z : ℂ} (hz : 0 < z.im) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᶠ w in 𝓝 z, boundaryCutoff ε w = 1 := by
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show 0 < z.im / 2 by linarith)).filter_mono nhdsWithin_le_nhds] with ε hε hzε
  filter_upwards [Complex.continuous_im.continuousAt.eventually (eventually_gt_nhds (show 2 * ε < z.im by linarith))] with w hw
  exact boundaryCutoff_one hε hw.le

private theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {z : ℂ}
    (hz : z ∉ tsupport φ) : Laplacian.laplacian φ z = 0 := by
  exact image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_laplacian_subset φ h))

private theorem exists_bound_fderiv_of_contDiff_hasCompactSupport {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖fderiv ℝ φ z‖ ≤ D := by
  obtain ⟨D, hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuousOn
    ((hφ.continuous_fderiv (by norm_num)).continuousOn)
  refine ⟨max D 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (fderiv ℝ φ)
  · exact (hD z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact le_max_right _ _

private theorem tendsto_integral_boundaryCutoff_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℂ} {f : ℂ → F} (hf : IntegrableOn f {z : ℂ | 0 < z.im} μ) :
    Tendsto (fun ε => ∫ z in {z : ℂ | 0 < z.im}, boundaryCutoff ε z • f z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z in {z : ℂ | 0 < z.im}, f z ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖)
  · exact Eventually.of_forall (fun ε => (contDiff_boundaryCutoff ε).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  · exact Eventually.of_forall (fun ε => Eventually.of_forall (fun z => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (boundaryCutoff_mem_Icc ε z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (boundaryCutoff_mem_Icc ε z).2))
  · exact hf.norm
  · filter_upwards [ae_restrict_mem (isOpen_lt continuous_const Complex.continuous_im).measurableSet] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [boundaryCutoff_eventually_one hz] with ε hε
    rw [Filter.EventuallyEq.eq_of_nhds hε, one_smul]

private theorem tendsto_integral_laplacian_boundaryCutoff_mul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {φ : ℂ → ℝ} {f : ℂ → F} {D K : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hz : ∀ z : ℂ, z.im = 0 → φ z = 0)
    (hD : 0 ≤ D) (hφ1 : ∀ z, ‖fderiv ℝ φ z‖ ≤ D) (hK : 0 ≤ K)
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hfg : ∀ z ∈ tsupport φ, 0 < z.im → ‖f z‖ ≤ K * z.im) :
    Tendsto (fun ε => ∫ z in {z : ℂ | 0 < z.im},
      Laplacian.laplacian (fun w => boundaryCutoff ε w * φ w) z • f z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z in {z : ℂ | 0 < z.im}, Laplacian.laplacian φ z • f z ∂μ)) := by
  obtain ⟨A₀, hA₀⟩ := hc.exists_bound_of_continuousOn (continuous_laplacian hφ).continuousOn
  obtain ⟨R₀, hR₀⟩ := hc.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  let A := max A₀ 0
  let R := max R₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hR : 0 ≤ R := le_max_right _ _
  let C := A * K * R + 8 * CutoffProfile.derivBound * D * K
  let b : ℂ → ℝ := (tsupport φ).indicator (fun _ => C)
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hb : Integrable b (μ.restrict {z : ℂ | 0 < z.im}) := by
    apply (integrable_indicator_iff (isClosed_tsupport φ).measurableSet).mpr
    exact integrableOn_const (ne_of_lt ((Measure.restrict_le_self _).trans_lt hc.measure_lt_top))
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, 0 < z.im →
      ‖Laplacian.laplacian (fun w => boundaryCutoff ε w * φ w) z • f z‖ ≤ b z := by
    intro ε hε z hi
    by_cases hs : z ∈ tsupport φ
    · rw [show b z = C from indicator_of_mem hs _]
      have hRz : z.im ≤ R := (le_abs_self _).trans ((hR₀ z hs).trans (le_max_left _ _))
      have hAz : ‖Laplacian.laplacian φ z‖ ≤ A := (hA₀ z hs).trans (le_max_left _ _)
      have hg := boundaryCutoff_error_bound hε hD hK hi.le hφ.contDiffAt
        (norm_le_mul_im_of_zero_on_real (hφ.differentiable (by norm_num)) hφ1 hz hi.le)
        (hφ1 z) (hfg z hs hi)
      have hbz : ‖(boundaryCutoff ε z * Laplacian.laplacian φ z) • f z‖ ≤ A * K * R := by
        rw [norm_smul, norm_mul]
        have hχ : ‖boundaryCutoff ε z‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (boundaryCutoff_mem_Icc ε z).1]
          exact (boundaryCutoff_mem_Icc ε z).2
        calc
          _ ≤ (1 * A) * (K * R) := mul_le_mul
            (mul_le_mul hχ hAz (norm_nonneg _) zero_le_one)
            ((hfg z hs hi).trans (mul_le_mul_of_nonneg_left hRz hK))
            (norm_nonneg _) (by positivity)
          _ = _ := by ring
      calc
        _ ≤ ‖(Laplacian.laplacian (fun w => boundaryCutoff ε w * φ w) z -
            boundaryCutoff ε z * Laplacian.laplacian φ z) • f z‖ +
            ‖(boundaryCutoff ε z * Laplacian.laplacian φ z) • f z‖ := by
          rw [sub_smul]
          exact norm_le_norm_sub_add _ _
        _ ≤ 8 * CutoffProfile.derivBound * D * K + A * K * R := add_le_add hg hbz
        _ = C := by dsimp [C]; ring
    · rw [show b z = 0 from indicator_of_notMem hs _,
        laplacian_eq_zero_of_notMem_tsupport (fun h => hs (tsupport_mul_subset_right h)),
        zero_smul, norm_zero]
  apply tendsto_integral_filter_of_dominated_convergence b
  · apply Eventually.of_forall
    intro ε
    have hcε : ContDiff ℝ 2 (fun w => boundaryCutoff ε w * φ w) :=
      ((contDiff_boundaryCutoff ε).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).mul hφ
    exact (continuous_laplacian hcε).aestronglyMeasurable.smul (hf.aestronglyMeasurable hU)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem hU] with z hz
    exact hbound ε hε z hz
  · exact hb
  · filter_upwards [ae_restrict_mem hU] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [boundaryCutoff_eventually_one hz] with ε hε
    have he : (fun w => boundaryCutoff ε w * φ w) =ᶠ[𝓝 z] φ := by
      filter_upwards [hε] with w hw
      rw [hw, one_mul]
    rw [(laplacian_congr_nhds he).eq_of_nhds]

theorem integral_smul_laplacian_eq_integral_laplacian_smul_upper_half_plane
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    {φ : ℂ → ℝ} {f : ℂ → F} {K : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hz : ∀ z : ℂ, z.im = 0 → φ z = 0)
    (hf : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 f z)
    (hfg : ∀ z ∈ tsupport φ, 0 < z.im → ‖f z‖ ≤ K * z.im)
    (hI : IntegrableOn (fun z => φ z • Laplacian.laplacian f z) {z : ℂ | 0 < z.im} μ) :
    ∫ z in {z : ℂ | 0 < z.im}, φ z • Laplacian.laplacian f z ∂μ =
      ∫ z in {z : ℂ | 0 < z.im}, Laplacian.laplacian φ z • f z ∂μ := by
  obtain ⟨D, hD, hφ1⟩ := exists_bound_fderiv_of_contDiff_hasCompactSupport hφ hc
  have hright := tendsto_integral_laplacian_boundaryCutoff_mul hφ hc hz hD hφ1
    (le_max_right K 0) (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hs hz => (hfg z hs hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left K 0) hz.le)) (μ := μ)
  have hleft := tendsto_integral_boundaryCutoff_smul hI
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ z in {z : ℂ | 0 < z.im}, boundaryCutoff ε z • (φ z • Laplacian.laplacian f z) ∂μ) =
        ∫ z in {z : ℂ | 0 < z.im},
          Laplacian.laplacian (fun w => boundaryCutoff ε w * φ w) z • f z ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let ψ : ℂ → ℝ := fun w => boundaryCutoff ε w * φ w
    have hψ : ContDiff ℝ 2 ψ := ((contDiff_boundaryCutoff ε).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).mul hφ
    have hs : tsupport ψ ⊆ {z : ℂ | 0 < z.im} := by
      intro z hz
      exact (show 0 < ε from hε).trans_le
        (boundaryCutoff_tsupport_subset hε (tsupport_mul_subset_left hz))
    have hparts := integral_smul_laplacian_eq_integral_laplacian_smul hψ
      (hc.mul_left (f := boundaryCutoff ε)) (fun z hz => hf z (hs hz)) (μ := μ)
    simp only [← mul_smul]
    change (∫ z in {z : ℂ | 0 < z.im}, ψ z • Laplacian.laplacian f z ∂μ) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), zero_smul]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), zero_smul])]
    exact hparts
  exact tendsto_nhds_unique (hleft.congr' heq) hright

private theorem integrableOn_smul_laplacian_upper_half_plane_of_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {φ : ℂ → ℝ} {f : ℂ → F} {B : ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hf : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 f z)
    (hB : ∀ z ∈ tsupport φ, 0 < z.im → ‖Laplacian.laplacian f z‖ ≤ B) :
    IntegrableOn (fun z => φ z • Laplacian.laplacian f z) {z : ℂ | 0 < z.im} μ := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hl : ContinuousOn (Laplacian.laplacian f) {z : ℂ | 0 < z.im} := by
    exact fun z hz => (hf z hz).continuousAt_laplacian.continuousWithinAt
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left φ (Laplacian.laplacian f)).trans (subset_tsupport φ))).mp
  apply IntegrableOn.of_bound ((Measure.restrict_le_self _).trans_lt hc.measure_lt_top)
    ((hφ.continuousOn.smul hl).aestronglyMeasurable hU).restrict (max A 0 * max B 0)
  filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet,
    ae_restrict_of_ae (ae_restrict_mem hU)] with z hs hz
  change ‖φ z • Laplacian.laplacian f z‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul ((hA z hs).trans (le_max_left _ _))
    ((hB z hs hz).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

theorem integral_smul_laplacian_eq_integral_laplacian_smul_upper_half_plane_of_norm_laplacian_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    {φ : ℂ → ℝ} {f : ℂ → F} {K B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hz : ∀ z : ℂ, z.im = 0 → φ z = 0)
    (hf : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 f z)
    (hfg : ∀ z ∈ tsupport φ, 0 < z.im → ‖f z‖ ≤ K * z.im)
    (hB : ∀ z ∈ tsupport φ, 0 < z.im → ‖Laplacian.laplacian f z‖ ≤ B) :
    ∫ z in {z : ℂ | 0 < z.im}, φ z • Laplacian.laplacian f z ∂μ =
      ∫ z in {z : ℂ | 0 < z.im}, Laplacian.laplacian φ z • f z ∂μ :=
  integral_smul_laplacian_eq_integral_laplacian_smul_upper_half_plane hφ hc hz hf hfg
    (integrableOn_smul_laplacian_upper_half_plane_of_bound hφ.continuous hc hf hB)

end DifferentialGeometry.Analysis
