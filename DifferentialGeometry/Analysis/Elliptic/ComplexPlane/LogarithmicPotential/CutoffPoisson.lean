import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.TruncatedGradient
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacianRegularity
import DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis


/-- The literal annular error in the Laplacian of the cutoff logarithm. -/
def cutoffLogError (χ : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * (Real.log ‖z‖ * Laplacian.laplacian χ z +
    2 * (‖z‖ ^ 2)⁻¹ * fderiv ℝ χ z z)

private theorem contDiff_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (Laplacian.laplacian χ) := by
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ χ)) :=
    (hχ.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have he : Laplacian.laplacian χ = fun z => fderiv ℝ (fderiv ℝ χ) z 1 1 +
      fderiv ℝ (fderiv ℝ χ) z Complex.I Complex.I :=
    funext (laplacian_complex_eq_fderiv χ)
  rw [he]
  exact ((hdd.clm_apply contDiff_const).clm_apply contDiff_const).add
    ((hdd.clm_apply contDiff_const).clm_apply contDiff_const)

private theorem partial_contDiff {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem derivatives_zero_near_zero {χ : ℂ → ℝ}
    (hχ : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ)) :
    ∀ᶠ z in 𝓝 (0 : ℂ), fderiv ℝ χ z = 0 ∧ Laplacian.laplacian χ z = 0 := by
  have hD : fderiv ℝ χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℂ →L[ℝ] ℝ) := by
    filter_upwards [hχ.fderiv (𝕜 := ℝ)] with z hz
    simpa only [fderiv_const_apply] using hz
  have hDD := hD.fderiv (𝕜 := ℝ)
  filter_upwards [hD, hDD] with z hz hzz
  rw [fderiv_const_apply] at hzz
  refine ⟨hz, ?_⟩
  simp only [laplacian_complex_eq_fderiv, hzz, _root_.zero_apply, add_zero]

theorem cutoffLogError_eq_zero_near_zero {χ : ℂ → ℝ}
    (hχ : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ)) :
    cutoffLogError χ =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
  filter_upwards [derivatives_zero_near_zero hχ] with z hz
  simp only [cutoffLogError, hz.1, hz.2, _root_.zero_apply, mul_zero, add_zero]

theorem contDiff_cutoffLogError {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχone : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ)) :
    ContDiff ℝ ∞ (cutoffLogError χ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact contDiffAt_const.congr_of_eventuallyEq (cutoffLogError_eq_zero_near_zero hχone)
  · have hn : ContDiffAt ℝ ∞ (fun y : ℂ => ‖y‖) z := contDiffAt_id.norm ℝ hz
    have hlog := hn.log (norm_ne_zero_iff.mpr hz)
    have hinv := (hn.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
    exact contDiffAt_const.mul
      ((hlog.mul (contDiff_laplacian hχ).contDiffAt).add
        ((contDiffAt_const.mul hinv).mul
          ((hχ.fderiv_right (m := ∞) (by simp)).contDiffAt.clm_apply contDiffAt_id)))

theorem hasCompactSupport_cutoffLogError {χ : ℂ → ℝ}
    (hcχ : HasCompactSupport χ) : HasCompactSupport (cutoffLogError χ) := by
  apply hcχ.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  contrapose! hz
  have hL : Laplacian.laplacian χ z = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hz (tsupport_laplacian_subset χ h))
  simp [Function.mem_support, cutoffLogError, hL, fderiv_of_notMem_tsupport ℝ hz]

private theorem hasCompactSupport_truncatedLogKernel {χ : ℂ → ℝ}
    (hcχ : HasCompactSupport χ) : HasCompactSupport (truncatedLogKernel χ) := by
  have h : HasCompactSupport (fun z : ℂ => χ z * Real.log ‖z‖) := hcχ.mul_right
  exact h.mul_left

private theorem realLinear_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  rfl

private theorem fderiv_partial {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ χ y v) z w = fderiv ℝ (fderiv ℝ χ) z w v := by
  rw [fderiv_clm_apply ((hχ.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) z) (differentiableAt_const v)]
  simp

private theorem laplacian_product {χ φ : ℂ → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    Laplacian.laplacian (fun y => χ y * φ y) z =
      χ z * Laplacian.laplacian φ z + Laplacian.laplacian χ z * φ z +
        2 * (fderiv ℝ χ z 1 * fderiv ℝ φ z 1 +
          fderiv ℝ χ z Complex.I * fderiv ℝ φ z Complex.I) := by
  have he := congrArg (fderiv ℝ φ z)
    (Complex.orthonormalBasisOneI.sum_repr' (gradient χ z))
  simp only [inner_gradient_right, conj_trivial, Fin.sum_univ_two,
    Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  simp only [map_add, map_smul, smul_eq_mul] at he
  have h := (hχ.contDiffAt (x := z)).laplacian_fun_smul (hφ.contDiffAt (x := z))
  simp only [smul_eq_mul] at h
  rw [← he] at h
  exact h.trans (by ring)

private theorem cutoffLogError_as_partials {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (z : ℂ) :
    cutoffLogError χ z =
      2 * (truncatedLogGradient (fun y => fderiv ℝ χ y 1) z 1 +
        truncatedLogGradient (fun y => fderiv ℝ χ y Complex.I) z Complex.I) -
      truncatedLogKernel (Laplacian.laplacian χ) z := by
  change -(2 * Real.pi)⁻¹ * (Real.log ‖z‖ * Laplacian.laplacian χ z +
      2 * (‖z‖ ^ 2)⁻¹ * fderiv ℝ χ z z) =
    2 * (-(2 * Real.pi)⁻¹ *
      (Real.log ‖z‖ * fderiv ℝ (fun y => fderiv ℝ χ y 1) z 1 +
        fderiv ℝ χ z 1 * ((‖z‖ ^ 2)⁻¹ * ⟪z, (1 : ℂ)⟫_ℝ)) +
      -(2 * Real.pi)⁻¹ *
      (Real.log ‖z‖ * fderiv ℝ (fun y => fderiv ℝ χ y Complex.I) z Complex.I +
        fderiv ℝ χ z Complex.I * ((‖z‖ ^ 2)⁻¹ * ⟪z, Complex.I⟫_ℝ))) -
      -(2 * Real.pi)⁻¹ * (Laplacian.laplacian χ z * Real.log ‖z‖)
  rw [fderiv_partial hχ, fderiv_partial hχ, laplacian_complex_eq_fderiv,
    realLinear_apply (fderiv ℝ χ z) z]
  simp [real_inner_eq_re_inner]
  ring

/-- The actual cutoff logarithm has a delta source and its explicitly computed
smooth cutoff error. Both displayed scalar integrands are proved integrable. -/
theorem integrable_and_integral_truncatedLogKernel_laplacian_test
    {χ φ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχone : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ))
    (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun z : ℂ => truncatedLogKernel χ z * Laplacian.laplacian φ z) ∧
    Integrable (fun z : ℂ => φ z * cutoffLogError χ z) ∧
    (∫ z : ℂ, truncatedLogKernel χ z * Laplacian.laplacian φ z) =
      -φ 0 + ∫ z : ℂ, φ z * cutoffLogError χ z := by
  let d₁ (z : ℂ) := fderiv ℝ χ z 1
  let d₂ (z : ℂ) := fderiv ℝ χ z Complex.I
  let a (z : ℂ) := truncatedLogKernel χ z * Laplacian.laplacian φ z
  let b (z : ℂ) := truncatedLogKernel (Laplacian.laplacian χ) z * φ z
  let p₁ (z : ℂ) := truncatedLogKernel d₁ z * fderiv ℝ φ z 1
  let p₂ (z : ℂ) := truncatedLogKernel d₂ z * fderiv ℝ φ z Complex.I
  let q₁ (z : ℂ) := φ z * truncatedLogGradient d₁ z 1
  let q₂ (z : ℂ) := φ z * truncatedLogGradient d₂ z Complex.I
  have hd₁ := partial_contDiff hχ (1 : ℂ)
  have hd₂ := partial_contDiff hχ Complex.I
  have hi₁ := integrable_and_integral_truncatedLogKernel_directional_test
    (hd₁.of_le (by simp)) (hcχ.fderiv_apply ℝ 1) (hφ.of_le (by norm_num)) hcφ 1
  have hi₂ := integrable_and_integral_truncatedLogKernel_directional_test
    (hd₂.of_le (by simp)) (hcχ.fderiv_apply ℝ Complex.I)
    (hφ.of_le (by norm_num)) hcφ Complex.I
  change Integrable p₁ ∧ Integrable q₁ ∧ (∫ z, p₁ z) = -(∫ z, q₁ z) at hi₁
  change Integrable p₂ ∧ Integrable q₂ ∧ (∫ z, p₂ z) = -(∫ z, q₂ z) at hi₂
  have ha : Integrable a := by
    have hi := locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul (continuous_laplacian_complex hφ)) hcχ.mul_right
    convert hi.const_mul (-(2 * Real.pi)⁻¹) using 1
    ext z
    dsimp [a, truncatedLogKernel]
    ring
  have hb : Integrable b := by
    have hcL : HasCompactSupport (Laplacian.laplacian χ) :=
      hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset χ)
    have hi := locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
      ((contDiff_laplacian hχ).continuous.mul hφ.continuous)
      hcL.mul_right
    convert hi.const_mul (-(2 * Real.pi)⁻¹) using 1
    ext z
    dsimp [b, truncatedLogKernel]
    ring
  have hexp : (fun z : ℂ => -(2 * Real.pi)⁻¹ *
      (Real.log ‖z‖ * Laplacian.laplacian (fun y => χ y * φ y) z)) =
      fun z => a z + b z + 2 * (p₁ z + p₂ z) := by
    funext z
    rw [laplacian_product (hχ.of_le (by simp)) hφ]
    dsimp only [a, b, p₁, p₂, d₁, d₂, truncatedLogKernel]
    ring
  have herr : (fun z : ℂ => φ z * cutoffLogError χ z) =
      fun z => 2 * (q₁ z + q₂ z) - b z := by
    funext z
    rw [cutoffLogError_as_partials hχ]
    dsimp only [q₁, q₂, d₁, d₂, b]
    ring
  have hierr : Integrable (fun z : ℂ => φ z * cutoffLogError χ z) := by
    rw [herr]
    exact ((hi₁.2.1.add hi₂.2.1).const_mul 2).sub hb
  have hfund := integral_log_norm_mul_laplacian (f := fun y => χ y * φ y) hcχ.mul_right
    ((hχ.of_le (by simp) : ContDiff ℝ 2 χ).mul hφ)
  change (∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian (fun y => χ y * φ y) z) =
    (2 * Real.pi) * (χ 0 * φ 0) at hfund
  have hχ0 : χ 0 = 1 := hχone.self_of_nhds
  have hfund' : (∫ z : ℂ, -(2 * Real.pi)⁻¹ *
      (Real.log ‖z‖ * Laplacian.laplacian (fun y => χ y * φ y) z)) = -φ 0 := by
    rw [integral_const_mul, hfund, hχ0, one_mul]
    field_simp [Real.pi_ne_zero]
  rw [hexp, integral_add (f := fun z : ℂ => a z + b z)
    (g := fun z => 2 * (p₁ z + p₂ z)) (ha.add hb) ((hi₁.1.add hi₂.1).const_mul 2),
    integral_add ha hb, integral_const_mul, integral_add hi₁.1 hi₂.1,
    hi₁.2.2, hi₂.2.2] at hfund'
  refine ⟨ha, hierr, ?_⟩
  rw [herr, integral_sub (f := fun z : ℂ => 2 * (q₁ z + q₂ z))
    ((hi₁.2.1.add hi₂.2.1).const_mul 2) hb,
    integral_const_mul, integral_add hi₁.2.1 hi₂.2.1]
  change (∫ z, a z) = _
  linarith

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The potential is the literal Bochner convolution of the already constructed
cutoff kernel and the actual density. -/
def cutoffLogPotential (χ : ℂ → ℝ) (f : ℂ → F) : ℂ → F :=
  truncatedLogKernel χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

variable [CompleteSpace F]

private theorem integrable_and_integral_test_convolution
    {k : ℂ → ℝ} (hk : Integrable k) {f : ℂ → F} (hf : Integrable f)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun z : ℂ => ψ z • (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z) ∧
    Integrable (fun w : ℂ => (∫ y : ℂ, k y * ψ (y + w)) • f w) ∧
    (∫ z : ℂ, ψ z • (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z) =
      ∫ w : ℂ, (∫ y : ℂ, k y * ψ (y + w)) • f w := by
  let J (z w : ℂ) : F := ψ z • (k (z - w) • f w)
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ
  have hj : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hb := (hf.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ).flip hk).bdd_smul
      C (hψ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p : ℂ × ℂ => hC p.1)
    change Integrable (fun p : ℂ × ℂ => ψ p.1 • (k (p.1 - p.2) • f p.2))
      (volume.prod volume) at hb
    exact hb
  have hleft (z : ℂ) : (∫ w : ℂ, J z w) =
      ψ z • (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z := by
    rw [convolution_eq_swap]
    change (∫ w : ℂ, ψ z • (k (z - w) • f w)) = _
    rw [integral_smul]
    rfl
  have hright (w : ℂ) : (∫ z : ℂ, J z w) =
      (∫ y : ℂ, k y * ψ (y + w)) • f w := by
    calc
      _ = (∫ z : ℂ, ψ z * k (z - w)) • f w := by
        simp only [J, smul_smul, integral_smul_const]
      _ = _ := by
        rw [← integral_add_right_eq_self (fun z : ℂ => ψ z * k (z - w)) w]
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by simp only [add_sub_cancel_right, mul_comm]
  refine ⟨hj.integral_prod_left.congr (Eventually.of_forall hleft),
    hj.integral_prod_right.congr (Eventually.of_forall hright), ?_⟩
  calc
    _ = ∫ z : ℂ, ∫ w : ℂ, J z w :=
      integral_congr_ae (Eventually.of_forall fun z => (hleft z).symm)
    _ = ∫ w : ℂ, ∫ z : ℂ, J z w := integral_integral_swap hj
    _ = _ := integral_congr_ae (Eventually.of_forall hright)

private theorem laplacian_translate (φ : ℂ → ℝ) (w y : ℂ) :
    Laplacian.laplacian (fun z => φ (z + w)) y = Laplacian.laplacian φ (y + w) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_add_right]

/-- Actual translation and Bochner Fubini transfer the proved scalar kernel
identity to this same potential. No weak Poisson equation is supplied as data. -/
theorem weak_laplacian_cutoffLogPotential
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχone : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ))
    {f : ℂ → F} (hf : Continuous f) (hcf : HasCompactSupport f)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ z : ℂ, Laplacian.laplacian φ z • cutoffLogPotential χ f z) =
      ∫ z : ℂ, φ z • (-f z +
        (cutoffLogError χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z) := by
  have hk := integrable_truncatedLogKernel (hχ.of_le (by simp)) hcχ
  have hH := contDiff_cutoffLogError hχ hχone
  have hcH := hasCompactSupport_cutoffLogError hcχ
  have hiH : Integrable (cutoffLogError χ) := hH.continuous.integrable_of_hasCompactSupport hcH
  have hif : Integrable f := hf.integrable_of_hasCompactSupport hcf
  have hp := integrable_and_integral_test_convolution hk hif
    (continuous_laplacian_complex hφ)
    (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset φ))
  have he := integrable_and_integral_test_convolution hiH hif hφ.continuous hcφ
  obtain ⟨C, hC⟩ := hcφ.exists_bound_of_continuous hφ.continuous
  have hifφ : Integrable (fun z : ℂ => φ z • f z) :=
    hif.bdd_smul C hφ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hneg : Integrable (fun z : ℂ => -(φ z • f z)) := hifφ.neg
  have hshift (w : ℂ) :
      (∫ y : ℂ, truncatedLogKernel χ y * Laplacian.laplacian φ (y + w)) =
        -φ w + ∫ y : ℂ, cutoffLogError χ y * φ (y + w) := by
    have hφw : ContDiff ℝ 2 (fun y : ℂ => φ (y + w)) :=
      hφ.comp (contDiff_id.add contDiff_const)
    have hcφw : HasCompactSupport (fun y : ℂ => φ (y + w)) :=
      hcφ.comp_homeomorph (Homeomorph.addRight w)
    have ht := integrable_and_integral_truncatedLogKernel_laplacian_test hχ hcχ hχone hφw hcφw
    calc
      _ = -φ w + ∫ y : ℂ, φ (y + w) * cutoffLogError χ y := by
        simpa only [laplacian_translate, zero_add] using ht.2.2
      _ = _ := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  change (∫ z : ℂ, Laplacian.laplacian φ z •
    (truncatedLogKernel χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z) = _
  rw [hp.2.2]
  calc
    _ = ∫ w : ℂ, -(φ w • f w) +
        (∫ y : ℂ, cutoffLogError χ y * φ (y + w)) • f w := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        dsimp only
        rw [hshift, add_smul, neg_smul]
    _ = -(∫ w : ℂ, φ w • f w) +
        ∫ w : ℂ, (∫ y : ℂ, cutoffLogError χ y * φ (y + w)) • f w := by
      rw [integral_add hneg he.2.1, integral_neg]
    _ = -(∫ w : ℂ, φ w • f w) +
        ∫ z : ℂ, φ z • (cutoffLogError χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z := by
      rw [he.2.2]
    _ = _ := by
      simp only [smul_add, smul_neg]
      rw [integral_add hneg he.1, integral_neg]

/-- The compact literal logarithmic convolution gains two derivatives from
its proved weak equation and the existing Banach-valued Poisson engine. -/
theorem contDiff_two_cutoffLogPotential
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχone : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ))
    {f : ℂ → F} (hcf : HasCompactSupport f) {α K : ℝ≥0}
    (hf : HolderWith K α f) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiff ℝ 2 (cutoffLogPotential χ f) := by
  have hfc := hf.continuous hα
  have hk := integrable_truncatedLogKernel (hχ.of_le (by simp)) hcχ
  have hv : Continuous (cutoffLogPotential χ f) :=
    hcf.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hk.locallyIntegrable hfc
  have hcv : HasCompactSupport (cutoffLogPotential χ f) :=
    (hasCompactSupport_truncatedLogKernel hcχ).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hcf
  let e : ℂ → F := cutoffLogError χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have he : ContDiff ℝ ∞ e := (hasCompactSupport_cutoffLogError hcχ).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_cutoffLogError hχ hχone) hfc.locallyIntegrable
  have hce : HasCompactSupport e := (hasCompactSupport_cutoffLogError hcχ).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hcf
  obtain ⟨M, L, hM, hHe⟩ := Schauder.exists_norm_bound_and_holderWith_of_contDiff_hasCompactSupport
    (he.of_le (by simp)) hce hα1
  obtain ⟨B, hB⟩ := hcf.exists_bound_of_continuous hfc
  have hbound : ∀ z : ℂ, ‖-f z + e z‖ ≤ B + M := by
    intro z
    exact (norm_add_le _ _).trans (by rw [norm_neg]; exact add_le_add (hB z) (hM z))
  have hHolder : HolderWith (L + K) α (fun z : ℂ => -f z + e z) := by
    have hh : HolderWith (L + K) α (fun z : ℂ => e z - f z) :=
      Schauder.holderWith_sub hHe hf
    simpa only [sub_eq_add_neg, add_comm] using hh
  exact contDiff_two_of_holder_weak_laplacian hv hcv hbound
    (fun φ hφ hcφ => weak_laplacian_cutoffLogPotential hχ hcχ hχone hfc hcf φ hφ hcφ)
    hα hHolder

/-- A concrete smooth bump produces the cutoff, including the prescribed
region where the original logarithmic kernel is unchanged. -/
theorem exists_cutoff_contDiff_two_potential
    {f : ℂ → F} (hcf : HasCompactSupport f) {α K : ℝ≥0}
    (hf : HolderWith K α f) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 0 < L) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ)) ∧
      (∀ z : ℂ, ‖z‖ ≤ L → χ z = 1) ∧ ContDiff ℝ 2 (cutoffLogPotential χ f) := by
  let χ : ContDiffBump (0 : ℂ) := ⟨L, 2 * L, hL, by linarith⟩
  have hone : (χ : ℂ → ℝ) =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ) := χ.eventuallyEq_one
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, hone, ?_, ?_⟩
  · intro z hz
    exact χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_zero_right, χ] using hz)
  · exact contDiff_two_cutoffLogPotential χ.contDiff χ.hasCompactSupport hone hcf hf hα hα1

end Banach

end DifferentialGeometry.Analysis
