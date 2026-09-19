import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis

theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn
    {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {Ω : Set E} (hΩ : IsOpen Ω) {f φ : E → 𝕜}
    (hf : ContDiffOn ℝ 1 f Ω) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (v : E) :
    (∫ x in Ω, f x * fderiv ℝ φ x v ∂μ) = -∫ x in Ω, fderiv ℝ f x v * φ x ∂μ := by
  have hdφs : tsupport (fun x => fderiv ℝ φ x v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφs
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x v) := hφc.fderiv_apply (𝕜 := ℝ) v
  have hdc : ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint₁ : Integrable (fun x => fderiv ℝ f x v * φ x) μ :=
    ((hdc.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  have hint₂ : Integrable (fun x => f x * fderiv ℝ φ x v) μ :=
    ((hf.continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hdφs)).integrable_of_hasCompactSupport hdφc.mul_left
  have hint₃ : Integrable (fun x => f x * φ x) μ :=
    ((hf.continuousOn.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint₁ hint₂ hint₃
      (fun x hx => ((hf x (hφs hx)).contDiffAt (hΩ.mem_nhds (hφs hx))).differentiableAt
        one_ne_zero)
      (fun x _ => (hφ.differentiable one_ne_zero) x)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hφs h)), mul_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (f := fun x => fderiv ℝ φ x v) (fun h => hx (hdφs h)), mul_zero]

end DifferentialGeometry.Analysis
