import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeApproximation
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

private theorem weakSection_dbar_continuous {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) : Continuous (complexDbar φ) := by
  have hd := hφ.continuous_fderiv (by simp)
  exact ((hd.clm_apply continuous_const).add
    ((hd.clm_apply continuous_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

private theorem weakSection_dbar_support (φ : ℂ → ℂ) :
    tsupport (complexDbar φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hzφ
  apply hz
  simp only [complexDbar, fderiv_of_notMem_tsupport ℝ hzφ,
    zero_apply, smul_zero, add_zero]

private theorem weakSection_integrable_left
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {ξ : ℂ → V} (hξ : ContinuousOn ξ Ω)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => complexDbar φ z • ξ z) :=
  (hξ.locallyIntegrableOn hΩ.measurableSet).integrable_smul_left_of_hasCompactSupport
    (weakSection_dbar_continuous hφ)
    (hc.of_isClosed_subset isClosed_closure (weakSection_dbar_support φ))
    ((weakSection_dbar_support φ).trans hs)

private theorem weakSection_dbar_add {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    complexDbar (a + b) z = complexDbar a z + complexDbar b z := by
  simp only [complexDbar, fderiv_add ha hb, _root_.add_apply,
    smul_add]
  abel

private theorem weakSection_dbar_const_smul {a : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (c : ℂ) :
    complexDbar (c • a) z = c • complexDbar a z := by
  simp only [complexDbar, fderiv_const_smul ha c, _root_.smul_apply,
    smul_eq_mul]
  ring

private theorem weakSection_dbar_mul {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    complexDbar (a * b) z = complexDbar a z * b z + a z * complexDbar b z := by
  simp only [complexDbar, fderiv_mul ha hb, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

private theorem weakSection_complex_tests
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (ξ f : ℂ → V)
    (hξ : ContinuousOn ξ Ω) (hf : LocallyIntegrableOn f Ω volume)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ z, complexDbar (fun w => (ψ w : ℂ)) z • ξ z) =
        -(∫ z, (ψ z : ℂ) • f z))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ z, complexDbar φ z • ξ z) = -(∫ z, φ z • f z) := by
  let r : ℂ → ℝ := fun z => (φ z).re
  let s : ℂ → ℝ := fun z => (φ z).im
  let rc : ℂ → ℂ := fun z => (r z : ℂ)
  let sc : ℂ → ℂ := fun z => (s z : ℂ)
  have hr : ContDiff ℝ ∞ r := Complex.reCLM.contDiff.comp hφ
  have hsmooth : ContDiff ℝ ∞ s := Complex.imCLM.contDiff.comp hφ
  have hrc : ContDiff ℝ ∞ rc := Complex.ofRealCLM.contDiff.comp hr
  have hsc : ContDiff ℝ ∞ sc := Complex.ofRealCLM.contDiff.comp hsmooth
  have hrs : tsupport r ⊆ tsupport φ := by
    apply closure_mono
    intro z hz
    exact fun hzφ => hz (by simp [r, hzφ])
  have hss : tsupport s ⊆ tsupport φ := by
    apply closure_mono
    intro z hz
    exact fun hzφ => hz (by simp [s, hzφ])
  have hrcs : tsupport rc ⊆ tsupport φ := by
    apply closure_mono
    intro z hz
    exact fun hzφ => hz (by simp [rc, r, hzφ])
  have hscs : tsupport sc ⊆ tsupport φ := by
    apply closure_mono
    intro z hz
    exact fun hzφ => hz (by simp [sc, s, hzφ])
  have hrcC := hc.of_isClosed_subset isClosed_closure hrcs
  have hscC := hc.of_isClosed_subset isClosed_closure hscs
  have hir := weakSection_integrable_left hΩ hξ hrc hrcC (hrcs.trans hs)
  have his := weakSection_integrable_left hΩ hξ hsc hscC (hscs.trans hs)
  have hfr := hf.integrable_smul_left_of_hasCompactSupport hrc.continuous hrcC
    (hrcs.trans hs)
  have hfs := hf.integrable_smul_left_of_hasCompactSupport hsc.continuous hscC
    (hscs.trans hs)
  have her := hweak r hr (hc.of_isClosed_subset isClosed_closure hrs) (hrs.trans hs)
  have hes := hweak s hsmooth (hc.of_isClosed_subset isClosed_closure hss) (hss.trans hs)
  have heq : φ = rc + Complex.I • sc := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rc, sc, r, s]
    rw [mul_comm, Complex.re_add_im]
  have hd (z : ℂ) : complexDbar φ z =
      complexDbar rc z + Complex.I • complexDbar sc z := by
    rw [heq, weakSection_dbar_add (hrc.differentiable (by simp) z)
      ((hsc.differentiable (by simp) z).const_smul Complex.I),
      weakSection_dbar_const_smul (hsc.differentiable (by simp) z)]
  have hl : (fun z => complexDbar φ z • ξ z) =
      (fun z => complexDbar rc z • ξ z + Complex.I • (complexDbar sc z • ξ z)) := by
    funext z
    rw [hd, add_smul, smul_smul, smul_eq_mul]
  have hrgt : (fun z => φ z • f z) =
      (fun z => rc z • f z + Complex.I • (sc z • f z)) := by
    funext z
    conv_lhs => rw [heq]
    simp only [Pi.add_apply, Pi.smul_apply, add_smul, smul_smul, smul_eq_mul]
  have hisI : Integrable (fun z => Complex.I • (complexDbar sc z • ξ z)) :=
    his.smul Complex.I
  have hfsI : Integrable (fun z => Complex.I • (sc z • f z)) :=
    hfs.smul Complex.I
  rw [hl, hrgt, integral_add hir hisI, integral_smul,
    integral_add hfr hfsI, integral_smul, her, hes]
  simp only [smul_neg, neg_add]
  rfl

private theorem weakSection_scalar_product
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (ξ f : ℂ → ℂ)
    (hξ : ContinuousOn ξ Ω) (hf : LocallyIntegrableOn f Ω volume)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ z, complexDbar ψ z * ξ z) = -(∫ z, ψ z * f z))
    (b : ℂ → ℂ) (hb : ContDiff ℝ ∞ b)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => complexDbar φ z * (b z * ξ z)) ∧
      Integrable (fun z => φ z * (complexDbar b z * ξ z + b z * f z)) ∧
      (∫ z, complexDbar φ z * (b z * ξ z)) =
        -(∫ z, φ z * (complexDbar b z * ξ z + b z * f z)) := by
  have hleft : Integrable (fun z => complexDbar φ z * (b z * ξ z)) :=
    weakSection_integrable_left hΩ (hb.continuous.continuousOn.mul hξ) hφ hc hs
  have hder : Integrable (fun z => φ z * (complexDbar b z * ξ z)) :=
    (((weakSection_dbar_continuous hb).continuousOn.mul hξ).locallyIntegrableOn
      hΩ.measurableSet).integrable_smul_left_of_hasCompactSupport hφ.continuous hc hs
  have hforce : Integrable (fun z => φ z * (b z * f z)) :=
    (hf.continuousOn_mul hb.continuous.continuousOn hΩ.isLocallyClosed).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hc hs
  have heq := hweak (φ * b) (hφ.mul hb) hc.mul_right (tsupport_mul_subset_left.trans hs)
  have hld : (fun z => complexDbar (φ * b) z * ξ z) =
      (fun z => complexDbar φ z * (b z * ξ z) + φ z * (complexDbar b z * ξ z)) := by
    funext z
    rw [weakSection_dbar_mul (hφ.differentiable (by simp) z)
      (hb.differentiable (by simp) z)]
    ring
  have hrd : (fun z => (φ * b) z * f z) = (fun z => φ z * (b z * f z)) := by
    funext z
    exact mul_assoc _ _ _
  rw [hld, hrd, integral_add hleft hder] at heq
  have hr : (fun z => φ z * (complexDbar b z * ξ z + b z * f z)) =
      (fun z => φ z * (complexDbar b z * ξ z) + φ z * (b z * f z)) := by
    funext z
    exact mul_add _ _ _
  refine ⟨hleft, ?_, ?_⟩
  · rw [hr]
    exact hder.add hforce
  · rw [hr, integral_add hder hforce]
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      _ = ((∫ z, complexDbar φ z * (b z * ξ z)) +
          (∫ z, φ z * (complexDbar b z * ξ z))) +
          (∫ z, φ z * (b z * f z)) := by abel
      _ = 0 := by rw [heq, neg_add_cancel]

private theorem weakSection_dbar_clm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (L : V →L[ℂ] W) {g : ℂ → V} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    complexDbar (fun w => L (g w)) z = L (complexDbar g z) := by
  have hd : fderiv ℝ (fun w => L (g w)) z =
      (L.restrictScalars ℝ).comp (fderiv ℝ g z) :=
    ((L.restrictScalars ℝ).hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  simp only [complexDbar, hd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_add, map_smul]

private theorem weakSection_pair_apply (p : (ℂ × ℂ) →L[ℂ] ℂ)
    (T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (v : ℂ × ℂ) :
    p (T v) = p (T (1, 0)) * v.1 + p (T (0, 1)) * v.2 := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

private theorem weakSection_global_operator
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (ξ f : ℂ → ℂ × ℂ)
    (hξ : ContinuousOn ξ Ω) (hf : LocallyIntegrableOn f Ω volume)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ z, complexDbar (fun w => (ψ w : ℂ)) z • ξ z) =
        -(∫ z, (ψ z : ℂ) • f z))
    (B : ℂ → ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) (hB : ContDiff ℝ ∞ B)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => complexDbar φ z • B z (ξ z)) ∧
      Integrable (fun z => φ z • (complexDbar B z (ξ z) + B z (f z))) ∧
      (∫ z, complexDbar φ z • B z (ξ z)) =
        -(∫ z, φ z • (complexDbar B z (ξ z) + B z (f z))) := by
  have htest (p : (ℂ × ℂ) →L[ℂ] ℂ)
      (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
      (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω) :
      (∫ z, complexDbar ψ z * p (ξ z)) = -(∫ z, ψ z * p (f z)) := by
    have heq := congrArg p (weakSection_complex_tests hΩ ξ f hξ hf hweak hψ hcψ hsψ)
    rw [map_neg, ← p.integral_comp_comm (weakSection_integrable_left hΩ hξ hψ hcψ hsψ),
      ← p.integral_comp_comm
        (hf.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ hsψ)] at heq
    simpa only [map_smul, smul_eq_mul] using heq
  have hrow (p : (ℂ × ℂ) →L[ℂ] ℂ) :
      Integrable (fun z => p (complexDbar φ z • B z (ξ z))) ∧
        Integrable (fun z => p (φ z • (complexDbar B z (ξ z) + B z (f z)))) ∧
        (∫ z, p (complexDbar φ z • B z (ξ z))) =
          -(∫ z, p (φ z • (complexDbar B z (ξ z) + B z (f z)))) := by
    let L₁ : ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) →L[ℂ] ℂ :=
      p.comp (ContinuousLinearMap.apply ℂ (ℂ × ℂ) (1, 0))
    let L₂ : ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) →L[ℂ] ℂ :=
      p.comp (ContinuousLinearMap.apply ℂ (ℂ × ℂ) (0, 1))
    let b₁ : ℂ → ℂ := fun z => L₁ (B z)
    let b₂ : ℂ → ℂ := fun z => L₂ (B z)
    have hb₁ : ContDiff ℝ ∞ b₁ := (L₁.restrictScalars ℝ).contDiff.comp hB
    have hb₂ : ContDiff ℝ ∞ b₂ := (L₂.restrictScalars ℝ).contDiff.comp hB
    have hd₁ (z : ℂ) : complexDbar b₁ z = p (complexDbar B z (1, 0)) :=
      weakSection_dbar_clm L₁ (hB.differentiable (by simp) z)
    have hd₂ (z : ℂ) : complexDbar b₂ z = p (complexDbar B z (0, 1)) :=
      weakSection_dbar_clm L₂ (hB.differentiable (by simp) z)
    obtain ⟨hl₁, hr₁, he₁⟩ := weakSection_scalar_product hΩ
      (fun z => (ξ z).1) (fun z => (f z).1) hξ.fst
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).locallyIntegrableOn_comp hf)
      (htest (ContinuousLinearMap.fst ℂ ℂ ℂ)) b₁ hb₁ hφ hc hs
    obtain ⟨hl₂, hr₂, he₂⟩ := weakSection_scalar_product hΩ
      (fun z => (ξ z).2) (fun z => (f z).2) hξ.snd
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).locallyIntegrableOn_comp hf)
      (htest (ContinuousLinearMap.snd ℂ ℂ ℂ)) b₂ hb₂ hφ hc hs
    have hleft : (fun z => p (complexDbar φ z • B z (ξ z))) =
        (fun z => complexDbar φ z * (b₁ z * (ξ z).1) +
          complexDbar φ z * (b₂ z * (ξ z).2)) := by
      funext z
      rw [map_smul, weakSection_pair_apply]
      change complexDbar φ z * (b₁ z * (ξ z).1 + b₂ z * (ξ z).2) = _
      ring
    have hright : (fun z => p (φ z • (complexDbar B z (ξ z) + B z (f z)))) =
        (fun z => φ z * (complexDbar b₁ z * (ξ z).1 + b₁ z * (f z).1) +
          φ z * (complexDbar b₂ z * (ξ z).2 + b₂ z * (f z).2)) := by
      funext z
      rw [map_smul, map_add, weakSection_pair_apply p (complexDbar B z),
        weakSection_pair_apply p (B z), ← hd₁, ← hd₂]
      change φ z * ((complexDbar b₁ z * (ξ z).1 + complexDbar b₂ z * (ξ z).2) +
        (b₁ z * (f z).1 + b₂ z * (f z).2)) = _
      ring
    rw [hleft, hright]
    refine ⟨hl₁.add hl₂, hr₁.add hr₂, ?_⟩
    rw [integral_add hl₁ hl₂, integral_add hr₁ hr₂, he₁, he₂, neg_add]
  obtain ⟨hl₁, hr₁, he₁⟩ := hrow (ContinuousLinearMap.fst ℂ ℂ ℂ)
  obtain ⟨hl₂, hr₂, he₂⟩ := hrow (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hl : Integrable (fun z => complexDbar φ z • B z (ξ z)) :=
    integrable_prod.mpr ⟨hl₁, hl₂⟩
  have hr : Integrable (fun z => φ z • (complexDbar B z (ξ z) + B z (f z))) :=
    integrable_prod.mpr ⟨hr₁, hr₂⟩
  refine ⟨hl, hr, Prod.ext ?_ ?_⟩
  · simpa only [ContinuousLinearMap.coe_fst', fst_integral hl, Prod.fst_neg, fst_integral hr] using he₁
  · simpa only [ContinuousLinearMap.coe_snd', snd_integral hl, Prod.snd_neg, snd_integral hr] using he₂

/-- A continuous weak solution obeys the product rule for a locally smooth complex
linear multiplier. Only the test functions and the multiplier are differentiated. -/
theorem integral_complexDbar_smul_clm_apply_of_weak_equation
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (ξ f : ℂ → ℂ × ℂ)
    (hξ : ContinuousOn ξ Ω) (hf : LocallyIntegrableOn f Ω volume)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ z, complexDbar (fun w => (ψ w : ℂ)) z • ξ z) =
        -(∫ z, (ψ z : ℂ) • f z))
    (B : ℂ → ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) (hB : ContDiffOn ℝ ∞ B Ω)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => complexDbar φ z • B z (ξ z)) ∧
      Integrable (fun z => φ z • (complexDbar B z (ξ z) + B z (f z))) ∧
      (∫ z, complexDbar φ z • B z (ξ z)) =
        -(∫ z, φ z • (complexDbar B z (ξ z) + B z (f z))) := by
  obtain ⟨G, hG, _, hGB⟩ :=
    exists_contDiff_compactSupport_extension_on_isCompact hc hΩ hs hB
  have hlocal (z : ℂ) (hz : z ∈ tsupport φ) : G =ᶠ[𝓝 z] B :=
    hGB.filter_mono (nhds_le_nhdsSet hz)
  have hleft : (fun z => complexDbar φ z • G z (ξ z)) =
      (fun z => complexDbar φ z • B z (ξ z)) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(hlocal z hz).eq_of_nhds]
    · have hzero : complexDbar φ z = 0 := by
        simp only [complexDbar, fderiv_of_notMem_tsupport ℝ hz,
          zero_apply, smul_zero, add_zero]
      rw [hzero, zero_smul, zero_smul]
  have hright : (fun z => φ z • (complexDbar G z (ξ z) + G z (f z))) =
      (fun z => φ z • (complexDbar B z (ξ z) + B z (f z))) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · have hd : complexDbar G z = complexDbar B z := by
        simp only [complexDbar, (hlocal z hz).fderiv_eq]
      rw [hd, (hlocal z hz).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_smul, zero_smul]
  have hresult := weakSection_global_operator hΩ ξ f hξ hf hweak G hG hφ hc hs
  rwa [hleft, hright] at hresult


private theorem complexDbar_ringInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Q : ℂ → V →L[ℂ] V} {z : ℂ}
    (hQ : DifferentiableAt ℝ Q z) (hunit : IsUnit (Q z)) :
    complexDbar (fun w => Ring.inverse (Q w)) z =
      -(Ring.inverse (Q z) * complexDbar Q z * Ring.inverse (Q z)) := by
  obtain ⟨u, hu⟩ := hunit
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (V →L[ℂ] V) (↑u⁻¹) (↑u⁻¹)) (Q z) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have hd : fderiv ℝ (fun w => Ring.inverse (Q w)) z =
      (-ContinuousLinearMap.mulLeftRight ℝ (V →L[ℂ] V) (↑u⁻¹) (↑u⁻¹)).comp
        (fderiv ℝ Q z) := (hinv.comp z hQ.hasFDerivAt).fderiv
  have hui : (↑u⁻¹ : V →L[ℂ] V) = Ring.inverse (Q z) := by
    rw [← hu]
    simp
  simp only [complexDbar, hd, ContinuousLinearMap.comp_apply,
    _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui]
  simp only [smul_neg, ← neg_add, mul_add, add_mul,
    smul_mul_assoc, mul_smul_comm]

private theorem inverse_gauge_weak_residual
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Q : ℂ → V →L[ℂ] V} {z : ℂ}
    (hQ : DifferentiableAt ℝ Q z) (hunit : IsUnit (Q z))
    (A : V →L[ℂ] V) (v : V) :
    complexDbar (fun w => Ring.inverse (Q w)) z v + Ring.inverse (Q z) (A v) =
      Ring.inverse (Q z)
        ((A * Q z - complexDbar Q z) (Ring.inverse (Q z) v)) := by
  rw [complexDbar_ringInverse hQ hunit]
  have hcancel : Q z (Ring.inverse (Q z) v) = v := by
    change (Q z * Ring.inverse (Q z)) v = v
    rw [Ring.mul_inverse_cancel _ hunit]
    rfl
  simp only [_root_.neg_apply, mul_apply_eq_comp,
    _root_.sub_apply, map_sub, hcancel]
  abel

private theorem norm_inverse_gauge_weak_residual_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Q : ℂ → V →L[ℂ] V} {z : ℂ}
    (hQ : DifferentiableAt ℝ Q z) (hunit : IsUnit (Q z))
    (A : V →L[ℂ] V) (v : V) {L M : ℝ} (hL : 0 ≤ L)
    (hinv : ‖Ring.inverse (Q z)‖ ≤ L) (hval : ‖v‖ ≤ M) :
    ‖complexDbar (fun w => Ring.inverse (Q w)) z v + Ring.inverse (Q z) (A v)‖ ≤
      L ^ 2 * M * ‖A * Q z - complexDbar Q z‖ := by
  rw [inverse_gauge_weak_residual hQ hunit]
  calc
    _ ≤ ‖Ring.inverse (Q z)‖ *
        ‖(A * Q z - complexDbar Q z) (Ring.inverse (Q z) v)‖ :=
      (Ring.inverse (Q z)).le_opNorm _
    _ ≤ L * (‖A * Q z - complexDbar Q z‖ * (L * M)) := by
      apply mul_le_mul hinv _ (norm_nonneg _) hL
      exact ((A * Q z - complexDbar Q z).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left
          (((Ring.inverse (Q z)).le_opNorm _).trans
            (mul_le_mul hinv hval (norm_nonneg _) hL)) (norm_nonneg _))
    _ = _ := by ring

private theorem continuousOn_inverse_apply_of_isUnit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set ℂ} {P : ℂ → V →L[ℂ] V} {ξ : ℂ → V}
    (hP : ContinuousOn P Ω) (hξ : ContinuousOn ξ Ω)
    (hunit : ∀ z ∈ Ω, IsUnit (P z)) :
    ContinuousOn (fun z => Ring.inverse (P z) (ξ z)) Ω := by
  have hi : ContinuousOn (fun z => Ring.inverse (P z)) Ω := by
    intro z hz
    obtain ⟨u, hu⟩ := hunit z hz
    have hinv : ContinuousAt Ring.inverse (P z) := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact hinv.comp_continuousWithinAt (hP z hz)
  exact hi.clm_apply hξ

private theorem contDiffOn_inverse_of_isUnit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {Q : ℂ → V →L[ℂ] V}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hunit : ∀ z ∈ Ω, IsUnit (Q z)) :
    ContDiffOn ℝ ∞ (fun z => Ring.inverse (Q z)) Ω := by
  intro z hz
  obtain ⟨u, hu⟩ := hunit z hz
  have hi : ContDiffAt ℝ ∞ Ring.inverse (Q z) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact (hi.comp z (hQ.contDiffAt (hΩ.mem_nhds hz))).contDiffWithinAt

private theorem locallyIntegrableOn_bounded_operator_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {a : ℂ} {r C M : ℝ} {A : ℂ → V →L[ℂ] V} {ξ : ℂ → V}
    (hA : AEStronglyMeasurable A volume) (hξ : ContinuousOn ξ (Metric.ball a r))
    (hC : 0 ≤ C) (hbound : ∀ z, ‖A z‖ ≤ C)
    (hval : ∀ z ∈ Metric.ball a r, ‖ξ z‖ ≤ M) :
    LocallyIntegrableOn (fun z => A z (ξ z)) (Metric.ball a r) volume := by
  apply IntegrableOn.locallyIntegrableOn
  refine IntegrableOn.of_bound measure_ball_lt_top ?_ (C * M) ?_
  · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      hA.restrict (hξ.aestronglyMeasurable measurableSet_ball)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact ((A z).le_opNorm _).trans
      (mul_le_mul (hbound z) (hval z hz) (norm_nonneg _) hC)

private theorem integral_complexDbar_smul_inverse_continuous_gauge_eq_zero_of_approximation
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (P A : ℂ → (ℂ × ℂ) →L[ℂ] ℂ × ℂ) (ξ : ℂ → ℂ × ℂ)
    (Q : ℕ → ℂ → (ℂ × ℂ) →L[ℂ] ℂ × ℂ)
    (hξ : ContinuousOn ξ Ω)
    (hf : LocallyIntegrableOn (fun z => A z (ξ z)) Ω volume)
    (hξweak : ∀ (ψ : ℂ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ z, complexDbar (fun w => (ψ w : ℂ)) z • ξ z) =
        -(∫ z, (ψ z : ℂ) • A z (ξ z)))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hunit : ∀ n z, z ∈ Ω → IsUnit (Q n z))
    {L M : ℝ} (hL : 0 ≤ L)
    (hinv : ∀ n z, z ∈ Ω → ‖Ring.inverse (Q n z)‖ ≤ L)
    (hval : ∀ z ∈ Ω, ‖ξ z‖ ≤ M)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω)
    (hF : Integrable (fun z => complexDbar φ z • Ring.inverse (P z) (ξ z)))
    (happrox : Tendsto (fun n => ∫ z, ‖complexDbar φ z •
      (Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z))‖) atTop (𝓝 0))
    (hresInt : ∀ n, Integrable (fun z =>
      ‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖))
    (hresLim : Tendsto (fun n => ∫ z,
      ‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖) atTop (𝓝 0)) :
    (∫ z, complexDbar φ z • Ring.inverse (P z) (ξ z)) = 0 := by
  let F : ℂ → ℂ × ℂ := fun z => Ring.inverse (P z) (ξ z)
  let B : ℕ → ℂ → (ℂ × ℂ) →L[ℂ] ℂ × ℂ := fun n z => Ring.inverse (Q n z)
  let Fₙ : ℕ → ℂ → ℂ × ℂ := fun n z => B n z (ξ z)
  let E : ℕ → ℂ → ℂ × ℂ := fun n z =>
    complexDbar (B n) z (ξ z) + B n z (A z (ξ z))
  have hB (n : ℕ) : ContDiffOn ℝ ∞ (B n) Ω :=
    contDiffOn_inverse_of_isUnit hΩ (hQ n) (hunit n)
  have hInt (n : ℕ) := integral_complexDbar_smul_clm_apply_of_weak_equation
    hΩ ξ (fun z => A z (ξ z)) hξ hf hξweak (B n) (hB n) hφ hc hs
  have hnorm (n : ℕ) : ‖∫ z, φ z • E n z‖ ≤
      (L ^ 2 * M) * (∫ z, ‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖) := by
    calc
      _ ≤ ∫ z, ‖φ z • E n z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, (L ^ 2 * M) *
          (‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖) := by
        apply integral_mono_ae (hInt n).2.1.norm ((hresInt n).const_mul _)
        filter_upwards with z
        by_cases hz : z ∈ Ω
        · rw [norm_smul]
          calc
            _ ≤ ‖φ z‖ * (L ^ 2 * M * ‖A z * Q n z - complexDbar (Q n) z‖) :=
              mul_le_mul_of_nonneg_left
                (norm_inverse_gauge_weak_residual_le
                  (((hQ n).differentiableOn (by simp)).differentiableAt
                    (hΩ.mem_nhds hz))
                  (hunit n z hz) (A z) (ξ z) hL (hinv n z hz) (hval z hz))
                (norm_nonneg _)
            _ = _ := by ring
        · have hφz : φ z = 0 := by
            by_contra hn
            exact hz (hs (subset_tsupport φ hn))
          simp only [hφz, norm_zero, zero_smul, zero_mul, mul_zero, le_refl]
      _ = _ := integral_const_mul _ _
  have hEzero : Tendsto (fun n => ∫ z, φ z • E n z) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hnorm
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hresLim)
  have hJzero : Tendsto (fun n => ∫ z, complexDbar φ z • Fₙ n z) atTop (𝓝 0) := by
    have heq : (fun n => ∫ z, complexDbar φ z • Fₙ n z) =
        (fun n => -(∫ z, φ z • E n z)) := by
      funext n
      exact (hInt n).2.2
    rw [heq]
    simpa only [neg_zero] using hEzero.neg
  have hJlimit : Tendsto (fun n => ∫ z, complexDbar φ z • Fₙ n z) atTop
      (𝓝 (∫ z, complexDbar φ z • F z)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) ?_ happrox
    intro n
    rw [← integral_sub (hInt n).1 hF]
    simpa only [smul_sub] using norm_integral_le_integral_norm
      (fun z => complexDbar φ z • (Fₙ n z - F z))
  exact tendsto_nhds_unique hJlimit hJzero

/-- The same continuous bounded disk gauge cancels a continuous pair-valued section
with its actual smooth-test weak equation. No derivative of the section or of the
limiting gauge is required. -/
theorem disk_gauge_inverse_continuous_section_weak_equation
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (P : C(closedBall a R, (ℂ × ℂ) →L[ℂ] ℂ × ℂ)) (P₀ A : ℂ → (ℂ × ℂ) →L[ℂ] ℂ × ℂ)
    (hrep : ∀ z : closedBall a R, P₀ z = P z)
    (hA : AEStronglyMeasurable A volume)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hC : 0 ≤ C)
    (hnear : ∀ z ∈ closedBall a R, ‖P₀ z - 1‖ ≤ δ)
    (hbound : ∀ z, ‖A z‖ ≤ C)
    (hweak : ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ))))
    (ξ : ℂ → ℂ × ℂ) (hξ : ContinuousOn ξ (ball a R))
    (hξweak : ∀ (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • ξ z) =
        -(∫ z, (φ z : ℂ) • A z (ξ z))) :
    ContinuousOn (fun z => Ring.inverse (P₀ z) (ξ z)) (ball a (R / 2)) ∧
      ∀ (φ : ℂ → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball a (R / 2) →
        (∫ z, complexDbar φ z • Ring.inverse (P₀ z) (ξ z)) = 0 := by
  let χ := bufferedGaugeCutoff a R hR
  let Q : ℕ → ℂ → (ℂ × ℂ) →L[ℂ] ℂ × ℂ := fun n =>
    (bufferedGaugeBump R hR n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun z => χ z • P₀ z)
  obtain ⟨hQc, hQi, hPi, hweights⟩ := disk_gauge_has_controlled_mollifications
    a R hR P P₀ A hrep hA hδ0 hδ hC hnear hbound hweak
  have hsub : closedBall a (R / 2) ⊆ ball a R := by
    intro z hz
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hξsmall : ContinuousOn ξ (ball a (R / 2)) :=
    hξ.mono (ball_subset_closedBall.trans hsub)
  have hP₀ : ContinuousOn P₀ (closedBall a R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact P.continuous.congr fun z => (hrep z).symm
  have hsmallR : ball a (R / 2) ⊆ closedBall a R :=
    (ball_subset_closedBall.trans hsub).trans ball_subset_closedBall
  have hPc := hP₀.mono hsmallR
  have hFc : ContinuousOn (fun z => Ring.inverse (P₀ z) (ξ z)) (ball a (R / 2)) :=
    continuousOn_inverse_apply_of_isUnit hPc hξsmall
      (fun z hz => (hPi z (hsmallR hz)).1)
  obtain ⟨M, hM⟩ := (isCompact_closedBall a (R / 2)).exists_bound_of_continuousOn
    (hξ.mono hsub)
  let L := 1 / (1 - δ)
  have hL : 0 ≤ L := div_nonneg zero_le_one (sub_nonneg.mpr hδ.le)
  refine ⟨hFc, ?_⟩
  intro φ hφ hc hs
  have hd : Continuous (complexDbar φ) := by
    unfold complexDbar
    have hdf := hφ.continuous_fderiv (by simp)
    exact ((hdf.clm_apply continuous_const).add
      ((hdf.clm_apply continuous_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  have hdsub : tsupport (complexDbar φ) ⊆ tsupport φ := by
    apply closure_minimal _ isClosed_closure
    intro z hz
    by_contra hzφ
    have heq : complexDbar φ z = 0 := by
      simp only [complexDbar, fderiv_of_notMem_tsupport ℝ hzφ,
        zero_apply, smul_zero, add_zero]
    exact hz heq
  have hdc : HasCompactSupport (complexDbar φ) :=
    hc.of_isClosed_subset isClosed_closure hdsub
  have hψi : Integrable (fun z => ‖complexDbar φ z‖) :=
    (hd.integrable_of_hasCompactSupport hdc).norm
  have hψsupport : support (fun z => ‖complexDbar φ z‖) ⊆ ball a (R / 2) := by
    intro z hz
    exact hs (hdsub (subset_closure (norm_ne_zero_iff.mp hz)))
  obtain ⟨hPQi, hPQlim, _, _⟩ := hweights (fun z => ‖complexDbar φ z‖)
    hψi (fun _ => norm_nonneg _) hψsupport
  obtain ⟨_, _, hresi, hreslim⟩ := hweights (fun z => ‖φ z‖)
    (hφ.continuous.integrable_of_hasCompactSupport hc).norm
    (fun _ => norm_nonneg _) (by
      intro z hz
      exact hs (subset_closure (norm_ne_zero_iff.mp hz)))
  have hFi : Integrable (fun z => complexDbar φ z • Ring.inverse (P₀ z) (ξ z)) :=
    (hFc.locallyIntegrableOn isOpen_ball.measurableSet).integrable_smul_left_of_hasCompactSupport
      hd hdc (hdsub.trans hs)
  have hFni (n : ℕ) : Integrable
      (fun z => complexDbar φ z • Ring.inverse (Q n z) (ξ z)) := by
    have hFn := continuousOn_inverse_apply_of_isUnit (hQc n).continuous.continuousOn
      hξsmall (fun z hz => (hQi n z (ball_subset_closedBall hz)).1)
    have hlocal : LocallyIntegrableOn
        (fun z => Ring.inverse (Q n z) (ξ z)) (ball a (R / 2)) volume :=
      hFn.locallyIntegrableOn isOpen_ball.measurableSet
    exact hlocal.integrable_smul_left_of_hasCompactSupport hd hdc (hdsub.trans hs)
  have hdiffi (n : ℕ) : Integrable (fun z => ‖complexDbar φ z‖ *
      ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P₀ z) (ξ z)‖) := by
    simpa only [Pi.sub_apply, ← smul_sub, norm_smul] using ((hFni n).sub hFi).norm
  obtain ⟨_, hdiffLim⟩ := weighted_inverse_gauge_tendsto_zero volume P₀ Q ξ
    (fun z => ‖complexDbar φ z‖) hL
    (Eventually.of_forall fun z hz => by
      have hz' := hψsupport hz
      exact ⟨(hPi z (hsmallR hz')).1, (hPi z (hsmallR hz')).2,
        hM z (ball_subset_closedBall hz')⟩)
    (fun n => Eventually.of_forall fun z hz => hQi n z
      (ball_subset_closedBall (hψsupport hz)))
    (Eventually.of_forall fun _ => norm_nonneg _) hPQi
    (fun n => (hdiffi n).aestronglyMeasurable) hPQlim
  have hf : LocallyIntegrableOn (fun z => A z (ξ z)) (ball a (R / 2)) volume :=
    locallyIntegrableOn_bounded_operator_apply hA hξsmall hC hbound
      (fun z hz => hM z (ball_subset_closedBall hz))
  have hξweakSmall : ∀ (ψ : ℂ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball a (R / 2) →
      (∫ z, complexDbar (fun w => (ψ w : ℂ)) z • ξ z) =
        -(∫ z, (ψ z : ℂ) • A z (ξ z)) := by
    intro ψ hψ hψc hψs
    simpa only [complexDbar_ofReal ((hψ.differentiable (by simp)) _)] using
      hξweak ψ hψ hψc (hψs.trans (ball_subset_closedBall.trans hsub))
  apply integral_complexDbar_smul_inverse_continuous_gauge_eq_zero_of_approximation
    isOpen_ball P₀ A ξ Q hξsmall hf hξweakSmall
    (fun n => (hQc n).contDiffOn)
    (fun n z hz => (hQi n z (ball_subset_closedBall hz)).1) hL
    (fun n z hz => (hQi n z (ball_subset_closedBall hz)).2)
    (fun z hz => hM z (ball_subset_closedBall hz)) hφ hc hs hFi
    (by simpa only [norm_smul] using hdiffLim) hresi hreslim

end DifferentialGeometry.Analysis
