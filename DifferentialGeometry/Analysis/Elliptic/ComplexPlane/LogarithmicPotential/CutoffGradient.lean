import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.CutoffPoisson
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Convolution NNReal

namespace DifferentialGeometry.Analysis


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The scalar test is bounded before applying Fubini to the actual two L1
factors. This lemma does not presume any derivative of their convolution. -/
private theorem integral_test_convolution
    {k : ℂ → ℝ} (hk : Integrable k) {f : ℂ → F} (hf : Integrable f)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
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
  calc
    _ = ∫ z : ℂ, ∫ w : ℂ, J z w :=
      integral_congr_ae (Eventually.of_forall fun z => (hleft z).symm)
    _ = ∫ w : ℂ, ∫ z : ℂ, J z w := integral_integral_swap hj
    _ = _ := integral_congr_ae (Eventually.of_forall hright)

/-- The same logarithmic potential has the weak derivative obtained from the
proved scalar kernel identity. Both Fubini applications use genuine product L1. -/
private theorem integral_directional_test_cutoffLogPotential
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    {f : ℂ → F} (hf : Continuous f) (hcf : HasCompactSupport f)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : ℂ) :
    (∫ z : ℂ, fderiv ℝ φ z v • cutoffLogPotential χ f z) =
      -(∫ z : ℂ, φ z •
        ((fun y => truncatedLogGradient χ y v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z) := by
  have hk := integrable_truncatedLogKernel hχ hcχ
  have hΓ := (integrable_truncatedLogGradient hχ hcχ).apply_continuousLinearMap v
  have hif : Integrable f := hf.integrable_of_hasCompactSupport hcf
  have hdφ : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hp := integral_test_convolution hk hif hdφ (hcφ.fderiv_apply ℝ v)
  have hq := integral_test_convolution hΓ hif hφ.continuous hcφ
  have hshift (w : ℂ) :
      (∫ y : ℂ, truncatedLogKernel χ y * fderiv ℝ φ (y + w) v) =
        -(∫ y : ℂ, truncatedLogGradient χ y v * φ (y + w)) := by
    have hφw : ContDiff ℝ 1 (fun y : ℂ => φ (y + w)) :=
      hφ.comp (contDiff_id.add contDiff_const)
    have hcφw : HasCompactSupport (fun y : ℂ => φ (y + w)) :=
      hcφ.comp_homeomorph (Homeomorph.addRight w)
    have ht := integrable_and_integral_truncatedLogKernel_directional_test hχ hcχ hφw hcφw v
    simpa only [fderiv_comp_add_right, mul_comm] using ht.2.2
  change (∫ z : ℂ, fderiv ℝ φ z v •
    (truncatedLogKernel χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z) = _
  rw [hp, hq]
  calc
    _ = ∫ w : ℂ, -((∫ y : ℂ, truncatedLogGradient χ y v * φ (y + w)) • f w) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        dsimp only
        rw [hshift, neg_smul]
    _ = _ := integral_neg _

/-- The directional derivative of the literal cutoff-log potential is the
literal convolution with its proved L1 logarithmic gradient. Regularity is
derived by the actual Poisson theorem, not supplied as a hypothesis. -/
theorem fderiv_cutoffLogPotential_apply
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχone : χ =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ))
    {f : ℂ → F} (hcf : HasCompactSupport f) {α K : ℝ≥0}
    (hf : HolderWith K α f) (hα : 0 < α) (hα1 : α ≤ 1) (z v : ℂ) :
    fderiv ℝ (cutoffLogPotential χ f) z v =
      ∫ w : ℂ, truncatedLogGradient χ (z - w) v • f w := by
  have hfc : Continuous f := hf.continuous hα
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hp : ContDiff ℝ 2 (cutoffLogPotential χ f) :=
    contDiff_two_cutoffLogPotential hχ hcχ hχone hcf hf hα hα1
  let D (x : ℂ) : F := fderiv ℝ (cutoffLogPotential χ f) x v
  let G : ℂ → F :=
    (fun y => truncatedLogGradient χ y v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hDc : Continuous D :=
    (hp.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hΓ := (integrable_truncatedLogGradient hχ1 hcχ).apply_continuousLinearMap v
  have hGc : Continuous G := hcf.continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hΓ.locallyIntegrable hfc
  have he : D =ᵐ[volume] G := by
    apply ae_eq_of_integral_contDiff_smul_eq hDc.locallyIntegrable hGc.locallyIntegrable
    intro φ hφ hcφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
      (hφ1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hparts : (∫ x : ℂ, φ x • D x) =
        -(∫ x : ℂ, fderiv ℝ φ x v • cutoffLogPotential χ f x) := by
      apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      · exact hp.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hdφ (hcφ.fderiv_apply ℝ v)
      · exact hDc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hφ.continuous hcφ
      · exact hp.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hφ.continuous hcφ
      · intro x _
        exact hφ1.differentiable (by norm_num) x
      · intro x _
        exact hp.differentiable (by norm_num) x
    rw [hparts, integral_directional_test_cutoffLogPotential hχ1 hcχ hfc hcf hφ1 hcφ v,
      neg_neg]
  have hevery : D = G := Measure.eq_of_ae_eq he hDc hGc
  have hz := congrFun hevery z
  change fderiv ℝ (cutoffLogPotential χ f) z v = G z at hz
  dsimp only [G] at hz
  rw [convolution_eq_swap] at hz
  exact hz

end DifferentialGeometry.Analysis
