import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_mul_test
    {S : Set E} (hS : IsOpen S) {f φ : E → ℝ}
    (hf : ContinuousOn f S) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ S) :
    Integrable (fun x => f x * φ x) μ :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hS
    (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left

private theorem integral_mul_fderiv_eq_neg_of_contDiffOn
    {S : Set E} (hS : IsOpen S) {f φ : E → ℝ}
    (hf : ContDiffOn ℝ 1 f S) (v : E)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ S) :
    (∫ x in S, f x * fderiv ℝ φ x v ∂μ) =
      -∫ x in S, fderiv ℝ f x v * φ x ∂μ := by
  have hdφs : tsupport (fun x => fderiv ℝ φ x v) ⊆ S :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφs
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
    hφc.fderiv_apply (𝕜 := ℝ) v
  have hdc : ContinuousOn (fun x => fderiv ℝ f x v) S :=
    (hf.continuousOn_fderiv_of_isOpen hS le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint₁ := integrable_mul_test hS hdc hφ.continuous hφc hφs (μ := μ)
  have hint₂ := integrable_mul_test hS hf.continuousOn hdφ hdφc hdφs (μ := μ)
  have hint₃ := integrable_mul_test hS hf.continuousOn hφ.continuous hφc hφs (μ := μ)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint₁ hint₂ hint₃
      (fun x hx => ((hf x (hφs hx)).contDiffAt (hS.mem_nhds (hφs hx))).differentiableAt
        one_ne_zero)
      (fun x _ => (hφ.differentiable (by simp)) x)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)), mul_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hdφs h)), mul_zero]

theorem fderiv_eq_sum_of_weak_equation
    {ι : Type*} (s : Finset ι) {S : Set E} (hS : IsOpen S)
    {f : E → ℝ} {F : ι → E → ℝ} (v : E) (w : ι → E)
    (hf : ContDiffOn ℝ 1 f S) (hF : ∀ i ∈ s, ContDiffOn ℝ 1 (F i) S)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ S →
      (∫ x in S, f x * fderiv ℝ φ x v ∂μ) =
        ∑ i ∈ s, ∫ x in S, F i x * fderiv ℝ φ x (w i) ∂μ) :
    ∀ x ∈ S, fderiv ℝ f x v = ∑ i ∈ s, fderiv ℝ (F i) x (w i) := by
  classical
  let A : E → ℝ := fun x => fderiv ℝ f x v
  let B : E → ℝ := fun x => ∑ i ∈ s, fderiv ℝ (F i) x (w i)
  have hA : ContinuousOn A S :=
    (hf.continuousOn_fderiv_of_isOpen hS le_rfl).clm_apply continuousOn_const
  have hBi (i) (hi : i ∈ s) : ContinuousOn (fun x => fderiv ℝ (F i) x (w i)) S :=
    ((hF i hi).continuousOn_fderiv_of_isOpen hS le_rfl).clm_apply continuousOn_const
  have hB : ContinuousOn B S := continuousOn_finsetSum s hBi
  have hae : ∀ᵐ x ∂μ, x ∈ S → A x - B x = 0 := by
    apply hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hA.sub hB).locallyIntegrableOn hS.measurableSet)
    intro φ hφ hφc hφs
    have hAi := integrable_mul_test hS hA hφ.continuous hφc hφs (μ := μ)
    have hFi (i) (hi : i ∈ s) :
        Integrable (fun x => fderiv ℝ (F i) x (w i) * φ x) μ :=
      integrable_mul_test hS (hBi i hi) hφ.continuous hφc hφs
    have hsum : (∫ x in S, B x * φ x ∂μ) =
        ∑ i ∈ s, ∫ x in S, fderiv ℝ (F i) x (w i) * φ x ∂μ := by
      simp only [B, Finset.sum_mul]
      exact integral_finsetSum s (fun i hi => (hFi i hi).integrableOn)
    have heq := hweak φ hφ hφc hφs
    rw [integral_mul_fderiv_eq_neg_of_contDiffOn hS hf v hφ hφc hφs] at heq
    have hright : (∑ i ∈ s, ∫ x in S, F i x * fderiv ℝ φ x (w i) ∂μ) =
        -(∑ i ∈ s, ∫ x in S, fderiv ℝ (F i) x (w i) * φ x ∂μ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_mul_fderiv_eq_neg_of_contDiffOn hS (hF i hi) (w i) hφ hφc hφs
    rw [hright, ← hsum] at heq
    have heq' : (∫ x in S, A x * φ x ∂μ) = ∫ x in S, B x * φ x ∂μ :=
      neg_injective heq
    have hBi' := integrable_mul_test hS hB hφ.continuous hφc hφs (μ := μ)
    have hout : ∀ x ∉ S, φ x • (A x - B x) = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)), zero_smul]
    change (∫ x, φ x • (A x - B x) ∂μ) = 0
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    simp only [smul_eq_mul]
    have hproduct : (fun x => φ x * (A x - B x)) =
        fun x => A x * φ x - B x * φ x := by
      funext x
      ring
    rw [hproduct, integral_sub hAi.integrableOn hBi'.integrableOn, heq', sub_self]
  have hae' : A =ᵐ[μ.restrict S] B := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hS.measurableSet] with x hx hxS
    exact sub_eq_zero.mp (hx hxS)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hS hA hB


theorem fderiv_eq_sum_of_weak_equation_on_superset
    {ι : Type*} (s : Finset ι) {S T : Set E} (hS : IsOpen S) (hST : S ⊆ T)
    {f : E → ℝ} {F : ι → E → ℝ} (v : E) (w : ι → E)
    (hf : ContDiffOn ℝ 1 f S) (hF : ∀ i ∈ s, ContDiffOn ℝ 1 (F i) S)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ T →
      (∫ x in T, f x * fderiv ℝ φ x v ∂μ) =
        ∑ i ∈ s, ∫ x in T, F i x * fderiv ℝ φ x (w i) ∂μ) :
    ∀ x ∈ S, fderiv ℝ f x v = ∑ i ∈ s, fderiv ℝ (F i) x (w i) := by
  apply fderiv_eq_sum_of_weak_equation (μ := μ) s hS v w hf hF
  intro φ hφ hφc hφs
  have hintegral (a : E → ℝ) (z : E) :
      (∫ x in S, a x * fderiv ℝ φ x z ∂μ) =
        ∫ x in T, a x * fderiv ℝ φ x z ∂μ := by
    have hdφs : tsupport (fun x => fderiv ℝ φ x z) ⊆ S :=
      (tsupport_fderiv_apply_subset ℝ z).trans hφs
    have hzero (x : E) (hx : x ∉ S) : a x * fderiv ℝ φ x z = 0 := by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hdφs h)), mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x (fun h => hx (hST h)))]
  rw [hintegral f v]
  have hsum : (∑ i ∈ s, ∫ x in S, F i x * fderiv ℝ φ x (w i) ∂μ) =
      ∑ i ∈ s, ∫ x in T, F i x * fderiv ℝ φ x (w i) ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    exact hintegral (F i) (w i)
  rw [hsum]
  exact hweak φ hφ hφc (hφs.trans hST)

end DifferentialGeometry.Analysis.Distribution
