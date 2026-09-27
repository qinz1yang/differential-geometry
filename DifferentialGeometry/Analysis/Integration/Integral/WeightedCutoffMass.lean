import Mathlib.MeasureTheory.Integral.DominatedConvergence


open Filter
open scoped Topology

namespace MeasureTheory

variable {T M ι : Type*} [MeasurableSpace T] [MeasurableSpace M]
  {l : Filter ι} [l.IsCountablyGenerated]

theorem tendsto_integral_weighted_cutoff_mass
    (μ : Measure T) (ν : T → Measure M) (a : T → ℝ) (u : T → M → ℝ)
    (χ : ι → M → ℝ)
    (hχmeas : ∀ᶠ i in l, Measurable (χ i))
    (hχbound : ∀ᶠ i in l, ∀ x, ‖χ i x‖ ≤ 1)
    (hχone : ∀ x, Tendsto (fun i => χ i x) l (𝓝 1))
    (hu : ∀ᵐ t ∂μ, Integrable (u t) (ν t))
    (houter : ∀ᶠ i in l, AEStronglyMeasurable
      (fun t => a t * ∫ x, χ i x * u t x ∂ν t) μ)
    (hbound : Integrable (fun t => ‖a t‖ * ∫ x, ‖u t x‖ ∂ν t) μ) :
    Tendsto (fun i => ∫ t, a t * (∫ x, χ i x * u t x ∂ν t) ∂μ)
      l (𝓝 (∫ t, a t * (∫ x, u t x ∂ν t) ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖a t‖ * ∫ x, ‖u t x‖ ∂ν t) houter ?_ hbound ?_
  · filter_upwards [hχbound] with i hi
    filter_upwards [hu] with t ht
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply norm_integral_le_of_norm_le ht.norm
    exact ae_of_all (ν t) fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hi x)
  · filter_upwards [hu] with t ht
    have hmass : Tendsto (fun i => ∫ x, χ i x * u t x ∂ν t)
        l (𝓝 (∫ x, u t x ∂ν t)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun x => ‖u t x‖) ?_ ?_ ht.norm ?_
      · exact hχmeas.mono fun i hi =>
          hi.aestronglyMeasurable.mul ht.aestronglyMeasurable
      · exact hχbound.mono fun i hi => ae_of_all (ν t) fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hi x)
      · exact ae_of_all (ν t) fun x => by
          simpa only [one_mul] using (hχone x).mul_const (u t x)
    exact tendsto_const_nhds.mul hmass

theorem tendsto_integral_weighted_cutoff_mass_zero_of_const_mass
    (μ : Measure T) (ν : T → Measure M) (a : T → ℝ) (u : T → M → ℝ)
    (χ : ι → M → ℝ)
    (hχmeas : ∀ᶠ i in l, Measurable (χ i))
    (hχbound : ∀ᶠ i in l, ∀ x, ‖χ i x‖ ≤ 1)
    (hχone : ∀ x, Tendsto (fun i => χ i x) l (𝓝 1))
    (hu : ∀ᵐ t ∂μ, Integrable (u t) (ν t))
    (hunonneg : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, 0 ≤ u t x)
    (m : ℝ) (hmass : ∀ᵐ t ∂μ, (∫ x, u t x ∂ν t) = m)
    (ha : Integrable a μ) (hazero : (∫ t, a t ∂μ) = 0)
    (houter : ∀ᶠ i in l,
      AEStronglyMeasurable (fun t => ∫ x, χ i x * u t x ∂ν t) μ) :
    Tendsto (fun i => ∫ t, a t * (∫ x, χ i x * u t x ∂ν t) ∂μ)
      l (𝓝 0) := by
  have hnormmass : ∀ᵐ t ∂μ, (∫ x, ‖u t x‖ ∂ν t) = m := by
    filter_upwards [hunonneg, hmass] with t ht hmt
    rw [← hmt]
    apply integral_congr_ae
    filter_upwards [ht] with x hx
    exact Real.norm_of_nonneg hx
  have hbound : Integrable (fun t => ‖a t‖ * ∫ x, ‖u t x‖ ∂ν t) μ := by
    apply (ha.norm.mul_const m).congr
    filter_upwards [hnormmass] with t ht
    rw [ht]
  have hlim := tendsto_integral_weighted_cutoff_mass μ ν a u χ hχmeas hχbound
    hχone hu (houter.mono fun _ hi => ha.aestronglyMeasurable.mul hi) hbound
  have hzero : (∫ t, a t * (∫ x, u t x ∂ν t) ∂μ) = 0 := by
    calc
      (∫ t, a t * (∫ x, u t x ∂ν t) ∂μ) = ∫ t, a t * m ∂μ := by
        apply integral_congr_ae
        filter_upwards [hmass] with t ht
        rw [ht]
      _ = 0 := by rw [integral_mul_const, hazero, zero_mul]
  simpa only [hzero] using hlim

end MeasureTheory
