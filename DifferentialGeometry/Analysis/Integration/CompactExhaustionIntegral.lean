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

theorem integrable_compactExhaustionCutoff_mul
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hf : Integrable f μ) :
    ∀ n, Integrable
      (fun x => compactExhaustionCutoff (I := I) (M := M) K n x * f x) μ := by
  intro n
  let χ : M → ℝ := compactExhaustionCutoff (I := I) (M := M) K n
  have hχ : AEStronglyMeasurable χ μ :=
    (compactExhaustionCutoff_spec (I := I) (M := M) K n).1.continuous.aestronglyMeasurable
  have hχ_bound : ∀ᵐ x ∂μ, ‖χ x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    have hrange := (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.2.2
      (show χ x ∈ Set.range χ from ⟨x, rfl⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg hrange.1]
    exact hrange.2
  have hχf : Integrable (fun x => χ x * f x) μ :=
    hf.bdd_mul hχ hχ_bound
  simpa only [χ] using hχf

theorem integrable_one_sub_compactExhaustionCutoff_mul
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hf : Integrable f μ) :
    ∀ n, Integrable
      (fun x => (1 - compactExhaustionCutoff (I := I) (M := M) K n x) * f x) μ := by
  intro n
  have hsub := hf.sub (integrable_compactExhaustionCutoff_mul
    (I := I) (M := M) K hf n)
  change Integrable (fun x => f x -
    compactExhaustionCutoff (I := I) (M := M) K n x * f x) μ at hsub
  simpa only [sub_mul, one_mul] using hsub

theorem tendsto_integral_one_sub_compactExhaustionCutoff_mul
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hf : Integrable f μ) :
    Tendsto
      (fun n => ∫ x,
        (1 - compactExhaustionCutoff (I := I) (M := M) K n x) * f x ∂μ)
      atTop (𝓝 0) := by
  have hχ := tendsto_integral_compactExhaustionCutoff_mul
    (I := I) (M := M) K (μ := μ) (f := f) hf
  have hsub : Tendsto
      (fun n => (∫ x, f x ∂μ) -
        ∫ x, compactExhaustionCutoff (I := I) (M := M) K n x * f x ∂μ)
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ x, f x ∂μ) atTop
        (𝓝 (∫ x, f x ∂μ))).sub hχ)
  apply Filter.Tendsto.congr' _ hsub
  filter_upwards [] with n
  rw [show (fun x => (1 - compactExhaustionCutoff (I := I) (M := M) K n x) * f x) =
      (fun x => f x - compactExhaustionCutoff (I := I) (M := M) K n x * f x) by
        funext x
        ring]
  symm
  exact integral_sub hf (integrable_compactExhaustionCutoff_mul
    (I := I) (M := M) K hf n)

omit [BorelSpace M] in
theorem integral_one_sub_compactExhaustionCutoff_mul_nonneg
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hfnn : ∀ x, 0 ≤ f x) (n : ℕ) :
    0 ≤ ∫ x,
      (1 - compactExhaustionCutoff (I := I) (M := M) K n x) * f x ∂μ := by
  apply integral_nonneg
  intro x
  have hrange := (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.2.2
    (show compactExhaustionCutoff (I := I) (M := M) K n x ∈
      Set.range (compactExhaustionCutoff (I := I) (M := M) K n) from ⟨x, rfl⟩)
  exact mul_nonneg (sub_nonneg.mpr hrange.2) (hfnn x)

omit [BorelSpace M] in
theorem eventually_integral_one_sub_compactExhaustionCutoff_mul_eq_zero
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hsupp : HasCompactSupport f) :
    ∀ᶠ n in atTop, ∫ x,
      (1 - compactExhaustionCutoff (I := I) (M := M) K n x) * f x ∂μ = 0 := by
  have hone := compactExhaustionCutoff_eventually_one_on_compact
    (I := I) (M := M) K (tsupport f) hsupp.isCompact
  filter_upwards [hone] with n hn
  have hzero : (fun x => (1 - compactExhaustionCutoff (I := I) (M := M) K n x) * f x) =ᵐ[μ]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport f
    · rw [hn x hx]
      ring
    · have hxf : f x = 0 := by
        by_contra hne
        exact hx (subset_closure (show x ∈ Function.support f from hne))
      rw [hxf]
      ring
  simpa using integral_congr_ae hzero

end DifferentialGeometry.Analysis
