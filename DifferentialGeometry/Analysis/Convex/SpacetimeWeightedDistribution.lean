import DifferentialGeometry.Analysis.Convex.SpacetimeDirectionalDistribution
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem exists_locallyIntegrableOn_sum_directional_second_derivative_prod_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure ℝ} {μ : Measure E}
    [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
    {κ : Type*} [Fintype κ] {f : ℝ × E → ℝ} {S : Set ℝ} {U : Set E}
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - B x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ Q : ℝ × E → ℝ, Measurable Q ∧ LocallyIntegrableOn Q (S ×ˢ U) (ν.prod μ) ∧
      (∀ p, Q p = (S ×ˢ U).indicator (fun z => ∑ k, a k z * limUnder atTop (fun n =>
        ((S ×ˢ U).indicator f (z.1, z.2 + h n • v k) -
          2 * (S ×ˢ U).indicator f z +
          (S ×ˢ U).indicator f (z.1, z.2 - h n • v k)) / (h n) ^ 2)) p) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
        (fun n => ∑ k, a k p *
          ((f (p.1, p.2 + h n • v k) - 2 * f p + f (p.1, p.2 - h n • v k)) /
            (h n) ^ 2)) atTop (𝓝 (Q p))) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ S ×ˢ U →
        (∀ p, 0 ≤ φ p) → (∀ k, ∀ p ∈ tsupport φ, 0 ≤ a k p) →
        (∫ p, f p * ∑ k, fderiv ℝ
          (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
          ∫ p, Q p * φ p ∂ν.prod μ := by
  classical
  choose q hqmeas hqint hqeq hqdiff hqcmp using fun k =>
    exists_locallyIntegrableOn_directional_second_derivative_prod_of_concave_sub_quadratic
      (ν := ν) (μ := μ) hfcont hS hU B hf (v k) h hh hne
  let Q : ℝ × E → ℝ := (S ×ˢ U).indicator (fun p => ∑ k, a k p * q k p)
  have hameas : ∀ k, Measurable ((S ×ˢ U).indicator (a k)) := by
    intro k
    simpa only [Set.piecewise_eq_indicator] using
      ((ha k).continuousOn.measurable_piecewise (g := (0 : ℝ × E → ℝ))
        continuousOn_const (hS.prod hU).measurableSet)
  have hQsum : Q = fun p => ∑ k, ((S ×ˢ U).indicator (a k)) p * q k p := by
    funext p
    by_cases hp : p ∈ S ×ˢ U <;> simp [Q, hp]
  have hQmeas : Measurable Q := by
    rw [hQsum]
    exact Finset.measurable_fun_sum Finset.univ fun k _ => (hameas k).mul (hqmeas k)
  have hrawint : LocallyIntegrableOn (fun p => ∑ k, a k p * q k p)
      (S ×ˢ U) (ν.prod μ) := by
    apply (locallyIntegrableOn_iff (hS.prod hU).isLocallyClosed).mpr
    intro K hKU hK
    apply integrable_finsetSum Finset.univ
    intro k hk
    exact ((hqint k).continuousOn_mul (ha k).continuousOn
      (hS.prod hU).isLocallyClosed).integrableOn_compact_subset hKU hK
  have hQint : LocallyIntegrableOn Q (S ×ˢ U) (ν.prod μ) :=
    hrawint.congr (ae_restrict_of_forall_mem (hS.prod hU).measurableSet
      fun p hp => (indicator_of_mem hp _).symm)
  have hQdiff : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
      (fun n => ∑ k, a k p *
        ((f (p.1, p.2 + h n • v k) - 2 * f p + f (p.1, p.2 - h n • v k)) /
          (h n) ^ 2)) atTop (𝓝 (Q p)) := by
    filter_upwards [ae_all_iff.mpr hqdiff] with p hp
    intro hpSU
    change Tendsto _ atTop (𝓝 ((S ×ˢ U).indicator _ p))
    rw [indicator_of_mem hpSU]
    exact tendsto_finsetSum Finset.univ fun k _ => (hp k hpSU).const_mul (a k p)
  refine ⟨Q, hQmeas, hQint, ?_, hQdiff, ?_⟩
  · intro p
    simp only [Q, hqeq]
  · intro φ hφ hφsupp hφSU hφnonneg hanonneg
    let ψ : κ → ℝ × E → ℝ := fun k p => a k p * φ p
    have hψ : ∀ k, ContDiff ℝ 2 (ψ k) := by
      intro k
      obtain ⟨aExt, haExt, _, heq⟩ := exists_contDiff_compactSupport_extension_on_isCompact
        hφsupp.isCompact (hS.prod hU) hφSU (ha k)
      have hproduct : (fun p => aExt p * φ p) = ψ k := by
        funext p
        by_cases hp : p ∈ tsupport φ
        · exact congrArg (fun z => z * φ p) (heq.self_of_nhdsSet hp)
        · simp only [ψ, image_eq_zero_of_notMem_tsupport hp, mul_zero]
      exact hproduct ▸ haExt.mul hφ
    have hψsupp : ∀ k, HasCompactSupport (ψ k) := fun _ => hφsupp.mul_left
    have hψSU : ∀ k, tsupport (ψ k) ⊆ S ×ˢ U := fun _ =>
      tsupport_mul_subset_right.trans hφSU
    have hψnonneg : ∀ k, ∀ p, 0 ≤ ψ k p := by
      intro k p
      by_cases hp : φ p = 0
      · simp only [ψ, hp, mul_zero, le_refl]
      · exact mul_nonneg (hanonneg k p (subset_tsupport φ hp)) (hφnonneg p)
    let J : κ → ℝ × E → ℝ := fun k p =>
      fderiv ℝ (fun z => fderiv ℝ (ψ k) z (0, v k)) p (0, v k)
    have hJcont : ∀ k, Continuous (J k) := by
      intro k
      have hD : ContDiff ℝ 1 (fun p => fderiv ℝ (ψ k) p (0, v k)) :=
        ((hψ k).fderiv_right (by norm_num)).clm_apply contDiff_const
      exact (hD.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hJsupp : ∀ k, HasCompactSupport (J k) := fun k =>
      ((hψsupp k).fderiv_apply ℝ (0, v k)).fderiv_apply ℝ (0, v k)
    have hJSU : ∀ k, tsupport (J k) ⊆ S ×ˢ U := fun k =>
      (tsupport_fderiv_apply_subset ℝ (0, v k)).trans
        ((tsupport_fderiv_apply_subset ℝ (0, v k)).trans (hψSU k))
    have hLint : ∀ k, Integrable (fun p => f p * J k p) (ν.prod μ) := by
      intro k
      apply (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_right f (J k)).trans (subset_tsupport (J k)))).mp
      exact ContinuousOn.integrableOn_compact (hJsupp k).isCompact
        ((hfcont.mono (hJSU k)).mul (hJcont k).continuousOn)
    have hRint : ∀ k, Integrable (fun p => q k p * ψ k p) (ν.prod μ) := by
      intro k
      apply (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_right (q k) (ψ k)).trans (subset_tsupport (ψ k)))).mp
      exact IntegrableOn.mul_continuousOn
        ((hqint k).integrableOn_compact_subset (hψSU k) (hψsupp k).isCompact)
        (hψ k).continuous.continuousOn (hψsupp k).isCompact
    have hcmp : ∀ k, (∫ p, f p * J k p ∂ν.prod μ) ≤
        ∫ p, q k p * ψ k p ∂ν.prod μ := fun k =>
      hqcmp k (ψ k) (hψ k) (hψsupp k) (hψSU k) (hψnonneg k)
    have hLsum : (∫ p, f p * ∑ k, J k p ∂ν.prod μ) =
        ∑ k, ∫ p, f p * J k p ∂ν.prod μ := by
      calc
        (∫ p, f p * ∑ k, J k p ∂ν.prod μ) =
            ∫ p, ∑ k, f p * J k p ∂ν.prod μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun p => Finset.mul_sum _ _ _
        _ = _ := integral_finsetSum Finset.univ fun k _ => hLint k
    have hQmul : ∀ p, Q p * φ p = (∑ k, a k p * q k p) * φ p := by
      intro p
      by_cases hp : φ p = 0
      · simp only [hp, mul_zero]
      · simp only [Q, indicator_of_mem (hφSU (subset_tsupport φ hp))]
    have hRsum : (∫ p, Q p * φ p ∂ν.prod μ) =
        ∑ k, ∫ p, q k p * ψ k p ∂ν.prod μ := by
      calc
        (∫ p, Q p * φ p ∂ν.prod μ) = ∫ p, ∑ k, q k p * ψ k p ∂ν.prod μ := by
          apply integral_congr_ae
          apply Eventually.of_forall
          intro p
          change Q p * φ p = ∑ k, q k p * ψ k p
          rw [hQmul p, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          dsimp only [ψ]
          ring
        _ = _ := integral_finsetSum Finset.univ fun k _ => hRint k
    change (∫ p, f p * ∑ k, J k p ∂ν.prod μ) ≤ ∫ p, Q p * φ p ∂ν.prod μ
    rw [hLsum, hRsum]
    exact Finset.sum_le_sum fun k _ => hcmp k

theorem exists_locallyIntegrableOn_sum_directional_second_derivative_prod_of_concave_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure ℝ} {μ : Measure E}
    [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
    {κ : Type*} [Fintype κ] {f : ℝ × E → ℝ} {S : Set ℝ} {U : Set E}
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - B x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ) (ha : ∀ k, ContDiff ℝ 2 (a k))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ Q : ℝ × E → ℝ, Measurable Q ∧ LocallyIntegrableOn Q (S ×ˢ U) (ν.prod μ) ∧
      (∀ p, Q p = ∑ k, a k p * limUnder atTop (fun n =>
        ((S ×ˢ U).indicator f (p.1, p.2 + h n • v k) -
          2 * (S ×ˢ U).indicator f p +
          (S ×ˢ U).indicator f (p.1, p.2 - h n • v k)) / (h n) ^ 2)) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
        (fun n => ∑ k, a k p *
          ((f (p.1, p.2 + h n • v k) - 2 * f p + f (p.1, p.2 - h n • v k)) /
            (h n) ^ 2)) atTop (𝓝 (Q p))) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ S ×ˢ U →
        (∀ p, 0 ≤ φ p) → (∀ k, ∀ p ∈ tsupport φ, 0 ≤ a k p) →
        (∫ p, f p * ∑ k, fderiv ℝ
          (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
          ∫ p, Q p * φ p ∂ν.prod μ := by
  classical
  obtain ⟨Q, _, hQint, hQeq, hQdiff, hQcmp⟩ :=
    exists_locallyIntegrableOn_sum_directional_second_derivative_prod_of_contDiffOn
      (ν := ν) (μ := μ) hfcont hS hU B hf v a (fun k => (ha k).contDiffOn) h hh hne
  choose q hqmeas _ hqeq _ _ using fun k =>
    exists_locallyIntegrableOn_directional_second_derivative_prod_of_concave_sub_quadratic
      (ν := ν) (μ := μ) hfcont hS hU B hf (v k) h hh hne
  let R : ℝ × E → ℝ := fun p => ∑ k, a k p * q k p
  have hRmeas : Measurable R :=
    Finset.measurable_fun_sum Finset.univ fun k _ =>
      (ha k).continuous.measurable.mul (hqmeas k)
  have hRcanon : ∀ p, R p = ∑ k, a k p * limUnder atTop (fun n =>
      ((S ×ˢ U).indicator f (p.1, p.2 + h n • v k) -
        2 * (S ×ˢ U).indicator f p +
        (S ×ˢ U).indicator f (p.1, p.2 - h n • v k)) / (h n) ^ 2) := by
    intro p
    simp only [R, hqeq]
  have hRQ : ∀ p ∈ S ×ˢ U, R p = Q p := by
    intro p hp
    rw [hQeq p, indicator_of_mem hp]
    exact hRcanon p
  have hRint : LocallyIntegrableOn R (S ×ˢ U) (ν.prod μ) :=
    hQint.congr (ae_restrict_of_forall_mem (hS.prod hU).measurableSet
      fun p hp => (hRQ p hp).symm)
  refine ⟨R, hRmeas, hRint, hRcanon, ?_, ?_⟩
  · filter_upwards [hQdiff] with p hp
    intro hpSU
    rw [hRQ p hpSU]
    exact hp hpSU
  · intro φ hφ hφsupp hφSU hφnonneg hanonneg
    calc
      (∫ p, f p * ∑ k, fderiv ℝ
          (fun z => fderiv ℝ (fun y => a k y * φ y) z (0, v k)) p (0, v k) ∂ν.prod μ) ≤
          ∫ p, Q p * φ p ∂ν.prod μ := hQcmp φ hφ hφsupp hφSU hφnonneg hanonneg
      _ = ∫ p, R p * φ p ∂ν.prod μ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro p
        change Q p * φ p = R p * φ p
        by_cases hp : φ p = 0
        · simp only [hp, mul_zero]
        · rw [← hRQ p (hφSU (subset_tsupport φ hp))]

end DifferentialGeometry.Analysis.Calculus
