import DifferentialGeometry.Analysis.Integration.CompactExhaustionCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Set Filter MeasureTheory Topology Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

include I

theorem tendsto_integral_compactExhaustionCutoff_mul
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hf : Integrable f μ) :
    Tendsto
      (fun n => ∫ x, compactExhaustionCutoff (I := I) (M := M) K n x * f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let χ : ℕ → M → ℝ := fun n =>
    compactExhaustionCutoff (I := I) (M := M) K n
  have hχ_meas : ∀ n, AEStronglyMeasurable (χ n) μ := by
    intro n
    exact (compactExhaustionCutoff_spec (I := I) (M := M) K n).1.continuous.aestronglyMeasurable
  have hF_meas : ∀ n, AEStronglyMeasurable (fun x => χ n x * f x) μ := by
    intro n
    exact (hχ_meas n).mul hf.1
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖χ n x * f x‖ ≤ ‖f x‖ := by
    intro n
    filter_upwards [] with x
    have hrange := (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.2.2
      (show χ n x ∈ Set.range (χ n) from ⟨x, rfl⟩)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrange.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hrange.2
  have hpoint : ∀ x, Tendsto (fun n => χ n x * f x) atTop (𝓝 (f x)) := by
    intro x
    have hone : ∀ᶠ n in atTop, χ n x = 1 :=
      compactExhaustionCutoff_eventually_one_on_compact (I := I) (M := M) K
        {x} (isCompact_singleton : IsCompact ({x} : Set M)) |>.mono
          (fun n hn => hn x (mem_singleton x))
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hone] with n hn
    simp [hn]
  simpa only [χ] using
    (tendsto_integral_of_dominated_convergence (μ := μ) (fun x => ‖f x‖)
      hF_meas hf.norm hbound (Filter.Eventually.of_forall hpoint))

end DifferentialGeometry.Analysis
