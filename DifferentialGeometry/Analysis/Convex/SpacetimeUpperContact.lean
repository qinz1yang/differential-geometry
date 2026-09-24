import DifferentialGeometry.Analysis.Convex.SpacetimeWeightedDistribution
import DifferentialGeometry.Analysis.Calculus.Derivative.UpperContact
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure ℝ} {μ : Measure E}
  [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
  {κ : Type*} [Fintype κ] {f : ℝ × E → ℝ} {S : Set ℝ} {U : Set E}

theorem exists_spatial_second_derivative_le_of_ae_approximate_upper_contacts
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p) (B : ℝ × E → ℝ)
    (hcontact : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → ∀ ε : ℝ, 0 < ε → ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧ (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p + ε)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ Q : ℝ × E → ℝ, Measurable Q ∧ LocallyIntegrableOn Q (S ×ˢ U) (ν.prod μ) ∧
      (∀ p, Q p = (S ×ˢ U).indicator (fun z => ∑ k, a k z * limUnder atTop (fun n =>
        ((S ×ˢ U).indicator f (z.1, z.2 + h n • v k) -
          2 * (S ×ˢ U).indicator f z +
          (S ×ˢ U).indicator f (z.1, z.2 - h n • v k)) / (h n) ^ 2)) p) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Q p ≤ B p) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ S ×ˢ U →
        (∀ p, 0 ≤ φ p) →
        (∫ p, f p * ∑ k, fderiv ℝ
          (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
          ∫ p, Q p * φ p ∂ν.prod μ := by
  classical
  obtain ⟨Q, hQmeas, hQint, hQeq, _, hQcmp⟩ :=
    exists_locallyIntegrableOn_sum_directional_second_derivative_prod_of_contDiffOn
      (ν := ν) (μ := μ) hfcont hS hU A hf v a ha h hh hne
  choose q _ _ hqeq hqdiff _ using fun k =>
    exists_locallyIntegrableOn_directional_second_derivative_prod_of_concave_sub_quadratic
      (ν := ν) (μ := μ) hfcont hS hU A hf (v k) h hh hne
  have hQsum : ∀ p ∈ S ×ˢ U, Q p = ∑ k, a k p * q k p := by
    intro p hp
    rw [hQeq p, indicator_of_mem hp]
    simp only [hqeq]
  have hQle : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Q p ≤ B p := by
    filter_upwards [ae_all_iff.mpr hqdiff, hcontact] with p hp hpcontact
    intro hpSU
    have hbound : ∀ ε : ℝ, 0 < ε → Q p ≤ B p + ε := by
      intro ε hε
      obtain ⟨ψ, hψ, hle, heq, hsum⟩ := hpcontact hpSU ε hε
      rw [hQsum p hpSU]
      apply le_trans _ hsum
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (hanonneg k p hpSU)
      exact
        DifferentialGeometry.Analysis.directional_second_difference_limit_le_of_scalar_upper_contact
        (f := fun x => f (p.1, x)) (x := p.2) (v k) (hψ k) (hle k) (heq k)
        h hh (Eventually.of_forall hne) (hp k hpSU)
    by_contra hnot
    have hlt : B p < Q p := lt_of_not_ge hnot
    have hmid := hbound ((Q p - B p) / 2) (by linarith)
    linarith
  refine ⟨Q, hQmeas, hQint, hQeq, hQle, ?_⟩
  intro φ hφ hφsupp hφSU hφnonneg
  exact hQcmp φ hφ hφsupp hφSU hφnonneg fun k p hp => hanonneg k p (hφSU hp)

theorem exists_spatial_second_derivative_le_of_approximate_upper_contacts
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p) (B : ℝ × E → ℝ)
    (hcontact : ∀ p ∈ S ×ˢ U, ∀ ε : ℝ, 0 < ε → ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧ (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p + ε)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ Q : ℝ × E → ℝ, Measurable Q ∧ LocallyIntegrableOn Q (S ×ˢ U) (ν.prod μ) ∧
      (∀ p, Q p = (S ×ˢ U).indicator (fun z => ∑ k, a k z * limUnder atTop (fun n =>
        ((S ×ˢ U).indicator f (z.1, z.2 + h n • v k) -
          2 * (S ×ˢ U).indicator f z +
          (S ×ˢ U).indicator f (z.1, z.2 - h n • v k)) / (h n) ^ 2)) p) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Q p ≤ B p) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ S ×ˢ U →
        (∀ p, 0 ≤ φ p) →
        (∫ p, f p * ∑ k, fderiv ℝ
          (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
          ∫ p, Q p * φ p ∂ν.prod μ := by
  apply exists_spatial_second_derivative_le_of_ae_approximate_upper_contacts
    (ν := ν) (μ := μ) hfcont hS hU A hf v a ha hanonneg B
      (Eventually.of_forall hcontact) h hh hne

theorem exists_spatial_second_derivative_le_of_upper_contacts
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p) (B : ℝ × E → ℝ)
    (hcontact : ∀ p ∈ S ×ˢ U, ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧ (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ Q : ℝ × E → ℝ, Measurable Q ∧ LocallyIntegrableOn Q (S ×ˢ U) (ν.prod μ) ∧
      (∀ p, Q p = (S ×ˢ U).indicator (fun z => ∑ k, a k z * limUnder atTop (fun n =>
        ((S ×ˢ U).indicator f (z.1, z.2 + h n • v k) -
          2 * (S ×ˢ U).indicator f z +
          (S ×ˢ U).indicator f (z.1, z.2 - h n • v k)) / (h n) ^ 2)) p) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Q p ≤ B p) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ S ×ˢ U →
        (∀ p, 0 ≤ φ p) →
        (∫ p, f p * ∑ k, fderiv ℝ
          (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
          ∫ p, Q p * φ p ∂ν.prod μ := by
  apply exists_spatial_second_derivative_le_of_approximate_upper_contacts
    (ν := ν) (μ := μ) hfcont hS hU A hf v a ha hanonneg B ?_ h hh hne
  intro p hp ε hε
  obtain ⟨ψ, hψ, hle, heq, hbound⟩ := hcontact p hp
  exact ⟨ψ, hψ, hle, heq, by linarith⟩

theorem integral_sum_spatial_second_derivative_le_of_ae_approximate_upper_contacts
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p) (B : ℝ × E → ℝ)
    (hB : LocallyIntegrableOn B (S ×ˢ U) (ν.prod μ))
    (hcontact : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → ∀ ε : ℝ, 0 < ε → ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧ (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p + ε)
    (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφsupp : HasCompactSupport φ)
    (hφSU : tsupport φ ⊆ S ×ˢ U) (hφnonneg : ∀ p, 0 ≤ φ p) :
    (∫ p, f p * ∑ k, fderiv ℝ
      (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
      ∫ p, B p * φ p ∂ν.prod μ := by
  obtain ⟨Q, _, hQint, _, hQle, hQcmp⟩ :=
    exists_spatial_second_derivative_le_of_ae_approximate_upper_contacts
      (ν := ν) (μ := μ) hfcont hS hU A hf v a ha
      hanonneg B hcontact (fun n => 1 / ((n : ℝ) + 1))
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => by positivity)
  have hint : ∀ g : ℝ × E → ℝ, LocallyIntegrableOn g (S ×ˢ U) (ν.prod μ) →
      Integrable (fun p => g p * φ p) (ν.prod μ) := by
    intro g hg
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right g φ).trans (subset_tsupport φ))).mp
    exact IntegrableOn.mul_continuousOn
      (hg.integrableOn_compact_subset hφSU hφsupp.isCompact)
      hφ.continuous.continuousOn hφsupp.isCompact
  apply (hQcmp φ hφ hφsupp hφSU hφnonneg).trans
  apply integral_mono_ae (hint Q hQint) (hint B hB)
  filter_upwards [hQle] with p hp
  by_cases hpφ : φ p = 0
  · simp only [hpφ, mul_zero, le_refl]
  exact mul_le_mul_of_nonneg_right (hp (hφSU (subset_tsupport φ hpφ))) (hφnonneg p)

theorem integral_sum_spatial_second_derivative_le_of_approximate_upper_contacts
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p) (B : ℝ × E → ℝ)
    (hB : LocallyIntegrableOn B (S ×ˢ U) (ν.prod μ))
    (hcontact : ∀ p ∈ S ×ˢ U, ∀ ε : ℝ, 0 < ε → ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧ (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p + ε)
    (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφsupp : HasCompactSupport φ)
    (hφSU : tsupport φ ⊆ S ×ˢ U) (hφnonneg : ∀ p, 0 ≤ φ p) :
    (∫ p, f p * ∑ k, fderiv ℝ
      (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
      ∫ p, B p * φ p ∂ν.prod μ := by
  apply integral_sum_spatial_second_derivative_le_of_ae_approximate_upper_contacts
    (ν := ν) (μ := μ) hfcont hS hU A hf v a ha hanonneg B hB
      (Eventually.of_forall hcontact) φ hφ hφsupp hφSU hφnonneg

theorem integral_sum_spatial_second_derivative_le_of_upper_contacts
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p) (B : ℝ × E → ℝ)
    (hB : LocallyIntegrableOn B (S ×ˢ U) (ν.prod μ))
    (hcontact : ∀ p ∈ S ×ˢ U, ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧ (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p)
    (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφsupp : HasCompactSupport φ)
    (hφSU : tsupport φ ⊆ S ×ˢ U) (hφnonneg : ∀ p, 0 ≤ φ p) :
    (∫ p, f p * ∑ k, fderiv ℝ
      (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
      ∫ p, B p * φ p ∂ν.prod μ := by
  apply integral_sum_spatial_second_derivative_le_of_approximate_upper_contacts
    hfcont hS hU A hf v a ha hanonneg B hB ?_ φ hφ hφsupp hφSU hφnonneg
  intro p hp ε hε
  obtain ⟨ψ, hψ, hle, heq, hbound⟩ := hcontact p hp
  exact ⟨ψ, hψ, hle, heq, by linarith⟩

end DifferentialGeometry.Analysis.Calculus
