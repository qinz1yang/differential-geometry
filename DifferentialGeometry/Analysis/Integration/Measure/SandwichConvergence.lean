import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology ENNReal

namespace MeasureTheory

theorem tendsto_lintegral_of_dominated_convergence_of_measure_sandwich
    {X ι : Type*} [MeasurableSpace X] {l : Filter ι} [l.IsCountablyGenerated]
    {μ : Measure X} {ν : ι → Measure X} {c : ι → ℝ≥0∞}
    {F : ι → X → ℝ≥0∞} {f : X → ℝ≥0∞} (bound : X → ℝ≥0∞)
    (hmeas : ∀ᶠ i in l, Measurable (F i))
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, F i x ≤ bound x)
    (hfin : ∫⁻ x, bound x ∂μ ≠ ∞)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x)))
    (hc : Tendsto c l (𝓝 1))
    (hlower : ∀ᶠ i in l, μ ≤ ν i)
    (hupper : ∀ᶠ i in l, ν i ≤ c i • μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂ν i) l (𝓝 (∫⁻ x, f x ∂μ)) := by
  have hfixed := tendsto_lintegral_filter_of_dominated_convergence bound hmeas hbound hfin hlim
  have hright : Tendsto (fun i => c i * ∫⁻ x, F i x ∂μ) l (𝓝 (∫⁻ x, f x ∂μ)) := by
    simpa only [one_mul] using
      ENNReal.Tendsto.mul hc (Or.inl one_ne_zero) hfixed (Or.inr ENNReal.one_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfixed hright
  · filter_upwards [hlower] with i hi
    exact lintegral_mono' hi (fun _ => le_rfl)
  · filter_upwards [hupper] with i hi
    simpa only [lintegral_smul_measure, smul_eq_mul] using
      (lintegral_mono' hi (fun x => le_rfl : ∀ x, F i x ≤ F i x))

end MeasureTheory
