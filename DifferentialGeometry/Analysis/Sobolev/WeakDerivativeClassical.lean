import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

theorem fderiv_eq_sum_fderiv_add_of_weak_divergence
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {Ω : Set E} (hΩ : IsOpen Ω) (s : Finset ι) (v : E) (w : ι → E)
    {U F : E → ℝ} {V : ι → E → ℝ}
    (hU : ContDiffOn ℝ 1 U Ω) (hV : ∀ i ∈ s, ContDiffOn ℝ 1 (V i) Ω)
    (hF : ContinuousOn F Ω)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, U x * fderiv ℝ φ x v ∂μ) =
        (∑ i ∈ s, ∫ x in Ω, V i x * fderiv ℝ φ x (w i) ∂μ) - ∫ x in Ω, F x * φ x ∂μ) :
    ∀ x ∈ Ω, fderiv ℝ U x v = (∑ i ∈ s, fderiv ℝ (V i) x (w i)) + F x := by
  let DU := fun x => fderiv ℝ U x v
  let DV := fun i x => fderiv ℝ (V i) x (w i)
  let B := fun x => (∑ i ∈ s, DV i x) + F x
  have hDU : ContinuousOn DU Ω :=
    (hU.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hDV (i) (hi : i ∈ s) : ContinuousOn (DV i) Ω :=
    ((hV i hi).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hB : ContinuousOn B Ω := (continuousOn_finsetSum s hDV).add hF
  have hzero : ∀ᵐ x ∂μ.restrict Ω, x ∈ Ω → (DU - B) x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hDU.sub hB).locallyIntegrableOn hΩ.measurableSet)
    intro φ hφ hφc hφs
    have hint {A : E → ℝ} (hA : ContinuousOn A Ω) : Integrable (fun x => A x * φ x) (μ.restrict Ω) :=
      (((hA.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left).mono_measure
          Measure.restrict_le_self
    have h := hweak φ hφ hφc hφs
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn hΩ hU
      (hφ.of_le (by simp)) hφc hφs v] at h
    have hVi (i) (hi : i ∈ s) : (∫ x in Ω, V i x * fderiv ℝ φ x (w i) ∂μ) =
        -∫ x in Ω, DV i x * φ x ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn hΩ (hV i hi)
        (hφ.of_le (by simp)) hφc hφs (w i)
    have hsum := Finset.sum_congr rfl hVi
    rw [hsum, Finset.sum_neg_distrib] at h
    have hBI : (∫ x in Ω, B x * φ x ∂μ) =
        (∑ i ∈ s, ∫ x in Ω, DV i x * φ x ∂μ) + ∫ x in Ω, F x * φ x ∂μ := by
      simp only [B, add_mul, Finset.sum_mul]
      rw [integral_add (integrable_finsetSum s (fun i hi => hint (hDV i hi))) (hint hF),
        integral_finsetSum s (fun i hi => hint (hDV i hi))]
    simp only [Pi.sub_apply, smul_eq_mul]
    simp_rw [mul_comm (φ _), sub_mul]
    rw [integral_sub (hint hDU) (hint hB), hBI]
    change -(∫ x in Ω, DU x * φ x ∂μ) = _ at h
    linarith
  have hae : DU =ᵐ[μ.restrict Ω] B := by
    filter_upwards [hzero, ae_restrict_mem hΩ.measurableSet] with x hx hxs
    exact sub_eq_zero.mp (hx hxs)
  exact Measure.eqOn_open_of_ae_eq hae hΩ hDU hB

theorem ae_eq_fderiv_of_weak_deriv_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {Ω : Set E} (hΩ : IsOpen Ω) (v : E) {U R : E → ℝ}
    (hU : ContDiffOn ℝ 1 U Ω) (hR : LocallyIntegrableOn R Ω μ)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, U x * fderiv ℝ φ x v ∂μ) = -∫ x in Ω, R x * φ x ∂μ) :
    R =ᵐ[μ.restrict Ω] fun x => fderiv ℝ U x v := by
  let D := fun x => fderiv ℝ U x v
  have hD : ContinuousOn D Ω :=
    (hU.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hz : ∀ᵐ x ∂μ, x ∈ Ω → (R - D) x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hR.sub (hD.locallyIntegrableOn hΩ.measurableSet))
    intro φ hφ hφc hφs
    have hDI : Integrable (fun x => D x * φ x) μ :=
      ((hD.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
    have hRI : Integrable (fun x => R x * φ x) μ := by
      apply (integrableOn_iff_integrable_of_support_subset
        ((subset_tsupport (fun x => R x * φ x)).trans tsupport_mul_subset_right)).mp
      exact (hR.mul_continuousOn hφ.continuous.continuousOn hΩ.isLocallyClosed).integrableOn_compact_subset hφs hφc
    have h := hweak φ hφ hφc hφs
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn hΩ hU
      (hφ.of_le (by simp)) hφc hφs v] at h
    have hres (A : E → ℝ) : (∫ x in Ω, A x * φ x ∂μ) = ∫ x, A x * φ x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun hs => hx (hφs hs)), mul_zero]
    simp_rw [hres] at h
    simp only [Pi.sub_apply, smul_eq_mul]
    simp_rw [mul_comm (φ _), sub_mul]
    rw [integral_sub hRI hDI]
    change -(∫ x, D x * φ x ∂μ) = _ at h
    linarith
  change ∀ᵐ x ∂μ.restrict Ω, R x = D x
  rw [ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [hz] with x hx hxs
  exact sub_eq_zero.mp (hx hxs)

end DifferentialGeometry.Analysis.Sobolev
