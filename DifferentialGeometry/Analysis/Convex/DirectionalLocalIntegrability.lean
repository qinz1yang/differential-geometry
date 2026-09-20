import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrabilityTests
import DifferentialGeometry.Analysis.Convex.DirectionalSecondDerivative
import DifferentialGeometry.Analysis.Convex.IntegrableDirectionalDistribution

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ConcaveOn ℝ U (fun x => f x - B x x / 2))
    (v : E) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ q : E → ℝ, Measurable q ∧ LocallyIntegrableOn q U μ ∧
      (∀ x, q x = limUnder atTop (fun n =>
        (U.indicator f (x + h n • v) - 2 * U.indicator f x +
          U.indicator f (x - h n • v)) / (h n) ^ 2)) ∧
      ∀ᵐ x ∂μ, x ∈ U →
        Tendsto (fun n => (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
          atTop (𝓝 (q x)) := by
  obtain ⟨q, hqmeas, hqeq, hqdiff⟩ :=
    exists_measurable_directional_second_derivative_of_concave_sub_quadratic
      (μ := μ) hU B hf v h hh hne
  refine ⟨q, hqmeas, ?_, hqeq, hqdiff⟩
  apply MeasureTheory.locallyIntegrableOn_of_integrable_mul_contDiff (n := 2) hU
  intro φ hφ hφsupp hφU hφnonneg
  exact
    (integrable_mul_and_integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic
    B hf hU hφ hφsupp hφU hφnonneg v h hh hne hqdiff).1

end DifferentialGeometry.Analysis.Calculus
