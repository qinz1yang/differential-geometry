import DifferentialGeometry.Analysis.Viscosity.Differentiability
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts
import DifferentialGeometry.Analysis.Integration.Integral.CompactSupport
import DifferentialGeometry.Analysis.Integration.Lp.Lipschitz

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Viscosity

theorem distribution_le_of_upper_tests_of_locallyLipschitzOn_fderiv
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    [Fintype ι] [Fintype κ] {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u Ω) (hdu : LocallyLipschitzOn Ω (fderiv ℝ u))
    {a : ι → E → ℝ} {b : κ → E → ℝ} {c r : E → ℝ}
    (ha : ∀ i, ContDiffOn ℝ 2 (a i) Ω) (hb : ∀ j, ContDiffOn ℝ 1 (b j) Ω)
    (hc : LocallyIntegrableOn c Ω μ) (hr : LocallyIntegrableOn r Ω μ) (v w : ι → E) (z : κ → E)
    (hsub : ∀ x ∈ Ω, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x →
      -(∑ i, a i x * fderiv ℝ (fderiv ℝ ψ) x (v i) (w i)) +
        (∑ j, b j x * fderiv ℝ ψ x (z j)) + c x * u x ≤ r x)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∑ i, ∫ x in Ω, u x * fderiv ℝ (fderiv ℝ (fun y => a i y * φ y)) x (w i) (v i) ∂μ) -
      (∑ j, ∫ x in Ω, u x * fderiv ℝ (fun y => b j y * φ y) x (z j) ∂μ) +
      (∫ x in Ω, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
  have hu1 : ContDiffOn ℝ 1 u Ω := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).mpr
    exact ⟨hu, by norm_num, contDiffOn_zero.mpr hdu.continuousOn⟩
  have htesta (i : ι) : ContDiff ℝ 2 (fun x => a i x * φ x) :=
    ((ha i).mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  have htestb (j : κ) : ContDiff ℝ 1 (fun x => b j x * φ x) :=
    ((hb j).mul (hφ.of_le (by norm_num)).contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  have hAe : ∀ᵐ x ∂μ.restrict Ω,
      -(∑ i, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i)) +
        (∑ j, b j x * fderiv ℝ u x (z j)) + c x * u x - r x ≤ 0 := by
    apply ae_second_order_le_zero_of_upper_tests_of_locallyLipschitzOn_fderiv hΩ hu hdu
      (H := fun x p B => -(∑ i, a i x * B (v i) (w i)) + (∑ j, b j x * p (z j)) +
        c x * u x - r x)
    · intro x hx ψ hψ hm
      exact sub_nonpos.mpr (hsub x hx ψ hψ hm)
    · intro x hx
      exact (by fun_prop : Continuous (fun pair : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) =>
        -(∑ i, a i x * pair.2 (v i) (w i)) + (∑ j, b j x * pair.1 (z j)) +
          c x * u x - r x)).lowerSemicontinuous
  have hintA (i : ι) : IntegrableOn
      (fun x => a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x) Ω μ := by
    have h := (hdu.integrable_fderiv_fderiv_mul_of_hasCompactSupport (μ := μ) hΩ
      (htesta i).continuous hφc.mul_left (tsupport_mul_subset_right.trans hφs) (v i) (w i)).integrableOn (s := Ω)
    convert h using 1
    ext x
    ring
  have hintB (j : κ) : IntegrableOn (fun x => b j x * fderiv ℝ u x (z j) * φ x) Ω μ := by
    have hcont : ContinuousOn (fun x => b j x * fderiv ℝ u x (z j)) Ω :=
      (hb j).continuousOn.mul (hdu.continuousOn.clm_apply continuousOn_const)
    exact ((hcont.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport
        hφc.mul_left |>.integrableOn
  have hintC : IntegrableOn (fun x => (c x * u x - r x) * φ x) Ω μ := by
    have hup : Continuous (fun x => u x * φ x) :=
      (hu.continuousOn.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hφs)
    have h₁ := hc.integrable_smul_right_of_hasCompactSupport hup hφc.mul_left
      (tsupport_mul_subset_right.trans hφs)
    have h₂ := hr.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc hφs
    convert (h₁.sub h₂).integrableOn using 1
    ext x
    simp only [Pi.sub_apply, smul_eq_mul]
    ring
  have hineq : -(∑ i, ∫ x in Ω, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x ∂μ) +
      (∑ j, ∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ) +
      (∫ x in Ω, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
    have hsA := integrable_finsetSum Finset.univ (fun i _ => hintA i)
    have hsB := integrable_finsetSum Finset.univ (fun j _ => hintB j)
    have heq : (∫ x in Ω,
        (-(∑ i, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x) +
          (∑ j, b j x * fderiv ℝ u x (z j) * φ x)) + (c x * u x - r x) * φ x ∂μ) =
        -(∑ i, ∫ x in Ω, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x ∂μ) +
          (∑ j, ∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ) +
          (∫ x in Ω, (c x * u x - r x) * φ x ∂μ) := by
      have h₁ := integral_add (hsA.neg.add hsB) hintC
      have h₂ := integral_add hsA.neg hsB
      simp only [Pi.add_apply, Pi.neg_apply] at h₁ h₂
      rw [h₁, h₂, integral_neg, integral_finsetSum Finset.univ (fun i _ => hintA i),
        integral_finsetSum Finset.univ (fun j _ => hintB j)]
    rw [← heq]
    apply integral_nonpos_of_ae
    filter_upwards [hAe] with x hx
    have h := mul_nonpos_of_nonpos_of_nonneg hx (hφ0 x)
    simp only [Pi.zero_apply, sub_mul]
    simp only [add_mul, sub_mul, neg_mul, Finset.sum_mul] at h
    linarith
  have hA (i : ι) : (∫ x in Ω, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x ∂μ) =
      ∫ x in Ω, u x * fderiv ℝ (fderiv ℝ (fun y => a i y * φ y)) x (w i) (v i) ∂μ := by
    convert integral_fderiv_fderiv_mul_eq_of_locallyLipschitzOn_fderiv (μ := μ) hΩ hu hdu
      (htesta i) hφc.mul_left (tsupport_mul_subset_right.trans hφs) (v i) (w i) using 1
    congr 1
    ext x
    ring
  have hB (j : κ) : (∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ) =
      -∫ x in Ω, u x * fderiv ℝ (fun y => b j y * φ y) x (z j) ∂μ := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn (μ := μ) hΩ hu1
      (htestb j) hφc.mul_left (tsupport_mul_subset_right.trans hφs) (z j)
    have heq : (∫ x in Ω, fderiv ℝ u x (z j) * (b j x * φ x) ∂μ) =
        ∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ := by
      congr 1
      ext x
      ring
    rw [heq] at h
    linarith
  simp_rw [hA, hB, Finset.sum_neg_distrib] at hineq
  simpa only [sub_eq_add_neg] using hineq

end DifferentialGeometry.Analysis.Viscosity
