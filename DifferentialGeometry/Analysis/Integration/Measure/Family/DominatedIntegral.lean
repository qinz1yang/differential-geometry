import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {α β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_integral_zero_of_dominated_measure_family
    {l : Filter α} [l.IsCountablyGenerated]
    {μ : Measure β} {μs : α → Measure β} {F : α → β → E} {g : β → ℝ}
    (hμs : ∀ᶠ t in l, μs t ≤ μ)
    (hg : Integrable g μ)
    (hF_meas : ∀ᶠ t in l, AEStronglyMeasurable (F t) μ)
    (hF_bound : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖F t x‖ ≤ g x)
    (hF_limit : ∀ᵐ x ∂μ, Tendsto (fun t => F t x) l (𝓝 0)) :
    Tendsto (fun t => ∫ x, F t x ∂μs t) l (𝓝 0) := by
  have hnorm_limit : Tendsto (fun t => ∫ x, ‖F t x‖ ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence g
      (hF_meas.mono fun t ht => ht.norm)
      (hF_bound.mono fun t ht => by simpa only [norm_norm] using ht) hg
      (hF_limit.mono fun x hx => by simpa only [norm_zero] using hx.norm)
    simpa only [integral_zero] using h
  apply squeeze_zero_norm' _ hnorm_limit
  filter_upwards [hμs, hF_meas, hF_bound] with t hμ hFm hFb
  calc
    ‖∫ x, F t x ∂μs t‖ ≤ ∫ x, ‖F t x‖ ∂μs t := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖F t x‖ ∂μ := integral_mono_measure hμ
      (Eventually.of_forall fun x => norm_nonneg _) (hg.mono' hFm hFb).norm

end DifferentialGeometry.Analysis

end

noncomputable section

open Filter MeasureTheory Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure α} {μ : Measure β} [IsFiniteMeasure ν]

theorem integrable_integral_of_dominated_measure_family
    {μs : α → Measure β} {F : α → β → E} {g : β → ℝ}
    {χ : ℕ → β → ℝ}
    (hμs : ∀ᵐ t ∂ν, μs t ≤ μ)
    (hg : Integrable g μ)
    (hF_meas : ∀ᵐ t ∂ν, AEStronglyMeasurable (F t) (μs t))
    (hF_bound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μs t, ‖F t x‖ ≤ g x)
    (hχ_meas : ∀ᵐ t ∂ν, ∀ n, AEStronglyMeasurable (χ n) (μs t))
    (hχ_bound : ∀ᵐ t ∂ν, ∀ n, ∀ᵐ x ∂μs t, ‖χ n x‖ ≤ 1)
    (hχ_limit : ∀ᵐ t ∂ν, ∀ᵐ x ∂μs t, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hcut_meas : ∀ n, AEStronglyMeasurable
      (fun t => ∫ x, χ n x • F t x ∂μs t) ν) :
    Integrable (fun t => ∫ x, F t x ∂μs t) ν := by
  have hF_int : ∀ᵐ t ∂ν, Integrable (F t) (μs t) := by
    filter_upwards [hμs, hF_meas, hF_bound] with t hμ hFm hFb
    exact (hg.mono_measure hμ).mono' hFm hFb
  have hlimit : ∀ᵐ t ∂ν, Tendsto
      (fun n => ∫ x, χ n x • F t x ∂μs t) atTop
      (𝓝 (∫ x, F t x ∂μs t)) := by
    filter_upwards [hF_int, hχ_meas, hχ_bound, hχ_limit] with t hFi hχm hχb hχl
    apply tendsto_integral_of_dominated_convergence (fun x => ‖F t x‖)
    · intro n
      exact (hχm n).smul hFi.aestronglyMeasurable
    · exact hFi.norm
    · intro n
      filter_upwards [hχb n] with x hx
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
    · filter_upwards [hχl] with x hx
      simpa only [one_smul] using hx.smul_const (F t x)
  have hmeas : AEStronglyMeasurable (fun t => ∫ x, F t x ∂μs t) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop hcut_meas hlimit
  refine (integrable_const (∫ x, ‖g x‖ ∂μ)).mono' hmeas ?_
  filter_upwards [hμs, hF_bound, hF_int] with t hμ hFb hFi
  calc
    ‖∫ x, F t x ∂μs t‖ ≤ ∫ x, ‖F t x‖ ∂μs t := norm_integral_le_integral_norm _
    _ ≤ ∫ x, g x ∂μs t := integral_mono_ae hFi.norm (hg.mono_measure hμ) hFb
    _ ≤ ∫ x, ‖g x‖ ∂μs t := integral_mono_ae (hg.mono_measure hμ)
      (hg.norm.mono_measure hμ) (Eventually.of_forall fun x => Real.le_norm_self _)
    _ ≤ ∫ x, ‖g x‖ ∂μ := integral_mono_measure hμ
      (Eventually.of_forall fun x => norm_nonneg _) hg.norm

omit [MeasurableSpace α] [IsFiniteMeasure ν] in
theorem intervalIntegrable_integral_of_dominated_measure_family_on_Ioo
    {a b : ℝ} (hab : a ≤ b) {μ : Measure β}
    {μs : ℝ → Measure β} {F : ℝ → β → E} {g : β → ℝ}
    {χ : ℕ → β → ℝ}
    (hμs : ∀ t ∈ Set.Ioo a b, μs t ≤ μ)
    (hg : Integrable g μ)
    (hF_meas : ∀ t ∈ Set.Ioo a b, AEStronglyMeasurable (F t) (μs t))
    (hF_bound : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂μs t, ‖F t x‖ ≤ g x)
    (hχ_meas : ∀ t ∈ Set.Ioo a b, ∀ n, AEStronglyMeasurable (χ n) (μs t))
    (hχ_bound : ∀ t ∈ Set.Ioo a b, ∀ n, ∀ᵐ x ∂μs t, ‖χ n x‖ ≤ 1)
    (hχ_limit : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂μs t,
      Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hcut_cont : ∀ n, ContinuousOn
      (fun t => ∫ x, χ n x • F t x ∂μs t) (Set.Ioo a b)) :
    IntervalIntegrable (fun t => ∫ x, F t x ∂μs t) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
  apply integrable_integral_of_dominated_measure_family
    (μ := μ) (χ := χ)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hμs t ht
  · exact hg
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hF_meas t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hF_bound t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hχ_meas t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hχ_bound t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hχ_limit t ht
  · intro n
    exact (hcut_cont n).aestronglyMeasurable measurableSet_Ioo

end DifferentialGeometry.Analysis

end
