import DifferentialGeometry.Analysis.Integration.Integral.HalfPlaneLaplacian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace DifferentialGeometry.Analysis

def oddReflection {F : Type*} [AddGroup F] (f : ℂ → F) : ℂ → F :=
  {z : ℂ | 0 < z.im}.indicator f - {z : ℂ | z.im < 0}.indicator (f ∘ Complex.conjLIE)

theorem oddReflection_of_im_pos {F : Type*} [AddGroup F] (f : ℂ → F)
    {z : ℂ} (hz : 0 < z.im) : oddReflection f z = f z := by
  simp [oddReflection, hz, not_lt_of_ge hz.le]

theorem oddReflection_of_im_neg {F : Type*} [AddGroup F] (f : ℂ → F)
    {z : ℂ} (hz : z.im < 0) : oddReflection f z = -f (Complex.conjLIE z) := by
  simp [oddReflection, hz, not_lt_of_ge hz.le, Function.comp_apply]

theorem oddReflection_of_im_zero {F : Type*} [AddGroup F] (f : ℂ → F)
    {z : ℂ} (hz : z.im = 0) : oddReflection f z = 0 := by
  simp [oddReflection, hz]

theorem oddReflection_conj {F : Type*} [AddGroup F] (f : ℂ → F) (z : ℂ) :
    oddReflection f (Complex.conjLIE z) = -oddReflection f z := by
  have hi : (Complex.conjLIE z).im = -z.im := Complex.conj_im z
  have hinv : Complex.conjLIE (Complex.conjLIE z) = z := starRingEnd_self_apply z
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · rw [oddReflection_of_im_neg f (by rw [hi]; linarith), hinv, oddReflection_of_im_pos f hp]
  · rw [oddReflection_of_im_zero f hz.symm, oddReflection_of_im_zero f (by rw [hi, hz.symm, neg_zero]), neg_zero]
  · rw [oddReflection_of_im_pos f (by rw [hi]; linarith), oddReflection_of_im_neg f hn, neg_neg]

theorem oddReflection_eq_of_im_nonneg {F : Type*} [AddGroup F] (f : ℂ → F)
    (hzero : ∀ z : ℂ, z.im = 0 → f z = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    oddReflection f z = f z := by
  rcases hz.eq_or_lt with hz | hz
  · rw [oddReflection_of_im_zero f hz.symm, hzero z hz.symm]
  · exact oddReflection_of_im_pos f hz

theorem hasCompactSupport_oddReflection {F : Type*} [AddGroup F] {f : ℂ → F}
    (hc : HasCompactSupport f) : HasCompactSupport (oddReflection f) := by
  have hi (g : ℂ → F) (s : Set ℂ) (hg : HasCompactSupport g) :
      HasCompactSupport (s.indicator g) := by
    apply HasCompactSupport.intro hg
    intro z hz
    simp [indicator, image_eq_zero_of_notMem_tsupport hz]
  exact (hi f _ hc).sub (hi _ _ (hc.comp_homeomorph Complex.conjLIE.toHomeomorph))

theorem oddReflection_norm_le
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {K : ℝ}
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im) (z : ℂ) :
    ‖oddReflection f z‖ ≤ K * |z.im| := by
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · rw [oddReflection_of_im_pos f hp, abs_of_pos hp]
    exact hg z hp
  · rw [oddReflection_of_im_zero f hz.symm, norm_zero, hz.symm, abs_zero, mul_zero]
  · rw [oddReflection_of_im_neg f hn, norm_neg, abs_of_neg hn]
    simpa only [Complex.conjLIE_apply, Complex.conj_im] using
      hg (Complex.conjLIE z) (by simpa only [Complex.conjLIE_apply, Complex.conj_im, neg_pos] using hn)

theorem continuous_oddReflection_of_norm_le_mul_im
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {K : ℝ}
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im) :
    Continuous (oddReflection f) := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  apply continuous_iff_continuousAt.mpr
  intro z
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · have he : oddReflection f =ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hp] with w hw
      exact oddReflection_of_im_pos f hw
    exact (continuousAt_congr he).mpr ((hf z hp).continuousAt (hU.mem_nhds hp))
  · rw [ContinuousAt, oddReflection_of_im_zero f hz.symm]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : Tendsto (fun w : ℂ => K * |w.im|) (𝓝 z) (𝓝 0) := by
      have hh : Continuous (fun w : ℂ => K * |w.im|) :=
        continuous_const.mul Complex.continuous_im.abs
      simpa only [ContinuousAt, hz.symm, abs_zero, mul_zero] using hh.continuousAt (x := z)
    exact squeeze_zero (fun w => norm_nonneg _) (oddReflection_norm_le hg) hlim
  · have hcz : 0 < (Complex.conjLIE z).im := by
      simpa only [Complex.conjLIE_apply, Complex.conj_im, neg_pos] using hn
    have he : oddReflection f =ᶠ[𝓝 z] fun w => -f (Complex.conjLIE w) := by
      filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hn] with w hw
      exact oddReflection_of_im_neg f hw
    exact (continuousAt_congr he).mpr
      (((hf (Complex.conjLIE z) hcz).continuousAt (hU.mem_nhds hcz)).comp
        Complex.conjLIE.continuous.continuousAt).neg

private theorem integral_smul_oddReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F}
    (h₁ : IntegrableOn (fun z => φ z • f z) {z : ℂ | 0 < z.im})
    (h₂ : IntegrableOn (fun z => φ (Complex.conjLIE z) • f z) {z : ℂ | 0 < z.im}) :
    ∫ z : ℂ, φ z • oddReflection f z =
      ∫ z in {z : ℂ | 0 < z.im}, (φ z - φ (Complex.conjLIE z)) • f z := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hL : MeasurableSet {z : ℂ | z.im < 0} :=
    (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have hp : Complex.conjLIE ⁻¹' {z : ℂ | z.im < 0} = {z : ℂ | 0 < z.im} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, Complex.conjLIE_apply, Complex.conj_im, neg_lt_zero]
  have hpres := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjLIE.toHomeomorph.isClosedEmbedding.measurableEmbedding
  have hinv (z : ℂ) : Complex.conjLIE (Complex.conjLIE z) = z :=
    starRingEnd_self_apply z
  have hlow : IntegrableOn (fun z => φ z • f (Complex.conjLIE z)) {z : ℂ | z.im < 0} := by
    apply (hpres.integrableOn_comp_preimage hemb).mp
    change IntegrableOn (fun z => φ (Complex.conjLIE z) • f (Complex.conjLIE (Complex.conjLIE z)))
      (Complex.conjLIE ⁻¹' {z : ℂ | z.im < 0})
    simpa only [hp, hinv] using h₂
  have he (z : ℂ) : φ z • oddReflection f z =
      {z : ℂ | 0 < z.im}.indicator (fun z => φ z • f z) z -
      {z : ℂ | z.im < 0}.indicator (fun z => φ z • f (Complex.conjLIE z)) z := by
    by_cases hi : 0 < z.im <;> by_cases hl : z.im < 0 <;>
      simp [oddReflection, indicator, hi, hl, smul_sub, Function.comp_apply]
  simp_rw [he]
  rw [integral_sub ((integrable_indicator_iff hU).mpr h₁)
    ((integrable_indicator_iff hL).mpr hlow), integral_indicator hU, integral_indicator hL]
  have hchange := hpres.setIntegral_preimage_emb hemb
    (fun z => φ z • f (Complex.conjLIE z)) {z : ℂ | z.im < 0}
  simp only [hp, hinv] at hchange
  rw [← hchange, ← integral_sub h₁ h₂]
  apply integral_congr_ae
  filter_upwards with z
  rw [sub_smul]

private theorem integrableOn_smul_of_bound_on_tsupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {s : Set ℂ} {B : ℝ}
    (hs : MeasurableSet s) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hf : ContinuousOn f s)
    (hB : ∀ z ∈ tsupport φ, z ∈ s → ‖f z‖ ≤ B) :
    IntegrableOn (fun z => φ z • f z) s := by
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left φ f).trans (subset_tsupport φ))).mp
  apply IntegrableOn.of_bound ((Measure.restrict_le_self _).trans_lt hc.measure_lt_top)
    ((hφ.continuousOn.smul hf).aestronglyMeasurable hs).restrict (max A 0 * max B 0)
  filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet,
    ae_restrict_of_ae (ae_restrict_mem hs)] with z hz hzs
  change ‖φ z • f z‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul ((hA z hz).trans (le_max_left _ _))
    ((hB z hz hzs).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

private theorem integrableOn_smul_of_linear_growth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {K : ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im) :
    IntegrableOn (fun z => φ z • f z) {z : ℂ | 0 < z.im} := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  apply integrableOn_smul_of_bound_on_tsupport
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet hφ hc hf (B := max K 0 * max R 0)
  intro z hz hzs
  exact (hg z hzs).trans (mul_le_mul (le_max_left _ _)
    ((le_abs_self _).trans ((hR z hz).trans (le_max_left _ _))) hzs.le (le_max_right _ _))

theorem integral_laplacian_smul_oddReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {K B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hf : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 f z)
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im)
    (hB : ∀ z : ℂ, 0 < z.im → ‖Laplacian.laplacian f z‖ ≤ B) :
    ∫ z : ℂ, Laplacian.laplacian φ z • oddReflection f z =
      ∫ z : ℂ, φ z • oddReflection (Laplacian.laplacian f) z := by
  let ψ : ℂ → ℝ := fun z => φ z - φ (Complex.conjLIE z)
  have he : ContDiff ℝ 2 (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjCLE.contDiff
  have hψ : ContDiff ℝ 2 ψ := hφ.sub (hφ.comp he)
  have hcψ : HasCompactSupport ψ := hc.sub (hc.comp_homeomorph Complex.conjLIE.toHomeomorph)
  have hψ0 (z : ℂ) (hz : z.im = 0) : ψ z = 0 := by
    have hcj : Complex.conjLIE z = z := Complex.conj_eq_iff_im.mpr hz
    simp only [ψ, hcj, sub_self]
  have hψΔ (z : ℂ) : Laplacian.laplacian ψ z =
      Laplacian.laplacian φ z - Laplacian.laplacian φ (Complex.conjLIE z) := by
    change Laplacian.laplacian (φ - φ ∘ Complex.conjLIE) z = _
    rw [hφ.contDiffAt.laplacian_sub (hφ.comp he).contDiffAt]
    rw [Complex.conjLIE.laplacian_comp φ]
  have hfc : ContinuousOn f {z : ℂ | 0 < z.im} :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hΔc : ContinuousOn (Laplacian.laplacian f) {z : ℂ | 0 < z.im} := by
    exact fun z hz => (hf z hz).continuousAt_laplacian.continuousWithinAt
  have hcΔ : HasCompactSupport (Laplacian.laplacian φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset φ)
  have hΔφc := continuous_laplacian hφ
  rw [integral_smul_oddReflection
      (integrableOn_smul_of_linear_growth hΔφc hcΔ hfc hg)
      (integrableOn_smul_of_linear_growth (hΔφc.comp Complex.conjLIE.continuous)
        (hcΔ.comp_homeomorph Complex.conjLIE.toHomeomorph) hfc hg)]
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  rw [integral_smul_oddReflection
      (integrableOn_smul_of_bound_on_tsupport hU hφ.continuous hc hΔc (fun z _ hz => hB z hz))
      (integrableOn_smul_of_bound_on_tsupport hU (hφ.continuous.comp Complex.conjLIE.continuous)
        (hc.comp_homeomorph Complex.conjLIE.toHomeomorph) hΔc (fun z _ hz => hB z hz))]
  have hgreen := integral_smul_laplacian_eq_integral_laplacian_smul_upper_half_plane_of_norm_laplacian_le
    (μ := volume) hψ hcψ hψ0 hf (fun z _ hz => hg z hz) (fun z _ hz => hB z hz)
  simpa only [hψΔ] using hgreen.symm

end DifferentialGeometry.Analysis
