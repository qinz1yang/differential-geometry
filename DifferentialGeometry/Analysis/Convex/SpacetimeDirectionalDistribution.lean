import DifferentialGeometry.Analysis.Convex.DirectionalSecondDerivativeProduct
import DifferentialGeometry.Analysis.Integration.Integral.ProductComparison
import DifferentialGeometry.Analysis.Calculus.Derivative.ProductTest

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem integrable_mul_and_integral_mul_spatial_fderiv_fderiv_le_of_concaveOn_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure ℝ} {μ : Measure E}
    [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
    {f φ q : ℝ × E → ℝ} {S : Set ℝ} {U : Set E}
    (hfcont : ContinuousOn f (S ×ˢ U)) (hU : IsOpen U)
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - B x x / 2))
    (hqmeas : Measurable q) (hφ : ContDiff ℝ 2 φ) (hφsupp : HasCompactSupport φ)
    (hφSU : tsupport φ ⊆ S ×ˢ U) (hφnonneg : ∀ p, 0 ≤ φ p)
    (v : E) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hslice : ∀ t ∈ S, ∀ᵐ x ∂μ, x ∈ U → Tendsto
      (fun n => (f (t, x + h n • v) - 2 * f (t, x) + f (t, x - h n • v)) /
        (h n) ^ 2) atTop (𝓝 (q (t, x))))
    (hprod : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
      (fun n => (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) /
        (h n) ^ 2) atTop (𝓝 (q p))) :
    Integrable (fun p => q p * φ p) (ν.prod μ) ∧
      (∫ p, f p * fderiv ℝ (fun z => fderiv ℝ φ z (0, v)) p (0, v) ∂ν.prod μ) ≤
        ∫ p, q p * φ p ∂ν.prod μ := by
  let J : ℝ × E → ℝ := fun p =>
    fderiv ℝ (fun z => fderiv ℝ φ z (0, v)) p (0, v)
  have hD : ContDiff ℝ 1 (fun p => fderiv ℝ φ p (0, v)) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hJcont : Continuous J :=
    (hD.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJsupp : HasCompactSupport J :=
    (hφsupp.fderiv_apply ℝ (0, v)).fderiv_apply ℝ (0, v)
  have hJφ : tsupport J ⊆ tsupport φ :=
    (tsupport_fderiv_apply_subset ℝ (0, v)).trans
      (tsupport_fderiv_apply_subset ℝ (0, v))
  have hHint : Integrable (fun p => f p * J p) (ν.prod μ) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right f J).trans (subset_tsupport J))).mp
    exact ContinuousOn.integrableOn_compact hJsupp.isCompact
      ((hfcont.mono (hJφ.trans hφSU)).mul hJcont.continuousOn)
  have hGint : Integrable (fun p => B v v * φ p) (ν.prod μ) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφsupp).const_mul (B v v)
  have hφsliceU : ∀ t, tsupport (fun x => φ (t, x)) ⊆ U := by
    intro t x hx
    exact (hφSU (tsupport_comp_subset_preimage φ
      (continuous_const.prodMk continuous_id) hx)).2
  have hφzero : ∀ t, t ∉ S → ∀ x, φ (t, x) = 0 := by
    intro t ht x
    by_contra hx
    exact ht (hφSU (subset_tsupport φ hx)).1
  have hJzero : ∀ t, t ∉ S → ∀ x, J (t, x) = 0 := by
    intro t ht x
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    exact ht (hφSU (hJφ hx)).1
  have hresult : ∀ t ∈ S,
      Integrable (fun x => q (t, x) * φ (t, x)) μ ∧
      (∫ x, f (t, x) * J (t, x) ∂μ) ≤ ∫ x, q (t, x) * φ (t, x) ∂μ := by
    intro t ht
    have htφ : ContDiff ℝ 2 (fun x => φ (t, x)) := hφ.comp (contDiff_prodMk_right t)
    have hcmp := integrable_mul_and_integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic
      B (hf t ht) hU htφ (hφsupp.comp_prodMk_right t) (hφsliceU t)
      (fun x => hφnonneg (t, x)) v h hh hne (hslice t ht)
    simpa only [hφ.fderiv_fderiv_prodMk_right_apply, J] using hcmp
  have hFint : ∀ᵐ t ∂ν, Integrable (fun x => q (t, x) * φ (t, x)) μ := by
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ S
    · exact (hresult t ht).1
    · simpa only [hφzero t ht, mul_zero] using
        (integrable_const_iff.mpr (Or.inl rfl) : Integrable (fun _ : E => (0 : ℝ)) μ)
  have hFle : ∀ᵐ p ∂ν.prod μ, q p * φ p ≤ B v v * φ p := by
    filter_upwards [hprod] with p hp
    by_cases hpφ : φ p = 0
    · simp only [hpφ, mul_zero, le_refl]
    have hpSU := hφSU (subset_tsupport φ hpφ)
    exact mul_le_mul_of_nonneg_right
      (le_of_tendsto_second_central_difference_of_concaveOn_sub_quadratic
        B (hf p.1 hpSU.1) hU hpSU.2 v h hh hne (hp hpSU)) (hφnonneg p)
  have hHle : ∀ᵐ t ∂ν,
      (∫ x, f (t, x) * J (t, x) ∂μ) ≤ ∫ x, q (t, x) * φ (t, x) ∂μ := by
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ S
    · exact (hresult t ht).2
    · simp only [hφzero t ht, hJzero t ht, mul_zero, integral_zero, le_refl]
  exact MeasureTheory.integrable_prod_and_integral_le_of_fiber_integral_le
    (hqmeas.mul hφ.continuous.measurable).aestronglyMeasurable hGint hHint hFint hFle hHle

theorem exists_locallyIntegrableOn_directional_second_derivative_prod_of_concave_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure ℝ} {μ : Measure E}
    [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
    {f : ℝ × E → ℝ} {S : Set ℝ} {U : Set E}
    (hfcont : ContinuousOn f (S ×ˢ U))
    (hS : IsOpen S) (hU : IsOpen U) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - B x x / 2))
    (v : E) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ q : ℝ × E → ℝ, Measurable q ∧ LocallyIntegrableOn q (S ×ˢ U) (ν.prod μ) ∧
      (∀ p, q p = limUnder atTop (fun n =>
        ((S ×ˢ U).indicator f (p.1, p.2 + h n • v) -
          2 * (S ×ˢ U).indicator f p +
          (S ×ˢ U).indicator f (p.1, p.2 - h n • v)) / (h n) ^ 2)) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
        (fun n => (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) /
          (h n) ^ 2) atTop (𝓝 (q p))) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ S ×ˢ U →
        (∀ p, 0 ≤ φ p) →
        (∫ p, f p * fderiv ℝ (fun z => fderiv ℝ φ z (0, v)) p (0, v) ∂ν.prod μ) ≤
          ∫ p, q p * φ p ∂ν.prod μ := by
  classical
  let F : ℝ × E → ℝ := (S ×ˢ U).indicator f
  have hFmeas : Measurable F := by
    simpa only [Set.piecewise_eq_indicator, F] using
      (hfcont.measurable_piecewise (g := (0 : ℝ × E → ℝ))
        continuousOn_const (hS.prod hU).measurableSet)
  have hFconc : ∀ t ∈ S, ConcaveOn ℝ U (fun x => F (t, x) - B x x / 2) := by
    intro t ht
    apply (hf t ht).congr
    intro x hx
    simp only [F, indicator_of_mem (show (t, x) ∈ S ×ˢ U from ⟨ht, hx⟩)]
  obtain ⟨q, hqmeas, hqFeq, hsliceF, hprodF, _⟩ :=
    exists_measurable_directional_second_derivative_prod_of_concave_sub_quadratic
      (ν := ν) (μ := μ) hFmeas hS.measurableSet hU (fun _ => B) hFconc v h hh hne
  have hFind : ∀ t x, U.indicator (fun y => F (t, y)) x = F (t, x) := by
    intro t x
    by_cases hx : x ∈ U <;> simp [F, hx]
  have hqeq : ∀ p, q p = limUnder atTop (fun n =>
      ((S ×ˢ U).indicator f (p.1, p.2 + h n • v) -
        2 * (S ×ˢ U).indicator f p +
        (S ×ˢ U).indicator f (p.1, p.2 - h n • v)) / (h n) ^ 2) := by
    intro p
    simpa only [hFind, F] using hqFeq p
  have hevent : ∀ p ∈ S ×ˢ U,
      (fun n => (F (p.1, p.2 + h n • v) - 2 * F p + F (p.1, p.2 - h n • v)) /
        (h n) ^ 2) =ᶠ[atTop]
      (fun n => (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) /
        (h n) ^ 2) := by
    intro p hp
    have hp' : Tendsto (fun n => p.2 + h n • v) atTop (𝓝 p.2) := by
      simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hh.smul_const v)
    have hm' : Tendsto (fun n => p.2 - h n • v) atTop (𝓝 p.2) := by
      simpa only [zero_smul, sub_zero] using tendsto_const_nhds.sub (hh.smul_const v)
    filter_upwards [hp'.eventually (hU.mem_nhds hp.2),
      hm'.eventually (hU.mem_nhds hp.2)] with n hn hm
    simp only [F, indicator_of_mem hp,
      indicator_of_mem (show (p.1, p.2 + h n • v) ∈ S ×ˢ U from ⟨hp.1, hn⟩),
      indicator_of_mem (show (p.1, p.2 - h n • v) ∈ S ×ˢ U from ⟨hp.1, hm⟩)]
  have hslice : ∀ t ∈ S, ∀ᵐ x ∂μ, x ∈ U → Tendsto
      (fun n => (f (t, x + h n • v) - 2 * f (t, x) + f (t, x - h n • v)) /
        (h n) ^ 2) atTop (𝓝 (q (t, x))) := by
    intro t ht
    filter_upwards [hsliceF t ht] with x hx
    intro hxU
    exact (hx hxU).congr' (hevent (t, x) ⟨ht, hxU⟩)
  have hprod : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
      (fun n => (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) /
        (h n) ^ 2) atTop (𝓝 (q p)) := by
    filter_upwards [hprodF] with p hp
    intro hpSU
    exact (hp hpSU).congr' (hevent p hpSU)
  have hcmp : ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ S ×ˢ U → (∀ p, 0 ≤ φ p) →
      Integrable (fun p => q p * φ p) (ν.prod μ) ∧
      (∫ p, f p * fderiv ℝ (fun z => fderiv ℝ φ z (0, v)) p (0, v) ∂ν.prod μ) ≤
        ∫ p, q p * φ p ∂ν.prod μ := by
    intro φ hφ hφsupp hφSU hφnonneg
    exact integrable_mul_and_integral_mul_spatial_fderiv_fderiv_le_of_concaveOn_sub_quadratic
      hfcont hU B hf hqmeas hφ hφsupp hφSU hφnonneg v h hh hne hslice hprod
  refine ⟨q, hqmeas, ?_, hqeq, hprod, ?_⟩
  · exact MeasureTheory.locallyIntegrableOn_of_integrable_mul_contDiff (n := 2) (hS.prod hU)
      (fun φ hφ hφsupp hφSU hφnonneg => (hcmp φ hφ hφsupp hφSU hφnonneg).1)
  · intro φ hφ hφsupp hφSU hφnonneg
    exact (hcmp φ hφ hφsupp hφSU hφnonneg).2

end DifferentialGeometry.Analysis.Calculus
