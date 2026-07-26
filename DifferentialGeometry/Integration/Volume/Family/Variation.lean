import DifferentialGeometry.Integration.Volume.Family.Base
import DifferentialGeometry.Analysis.Integration.Measure.Family

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Clean volume variation formula

This file contains the clean-signature volume-variation theorem layer split
out of `DifferentialGeometry.Integral.Measure.Family`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Canonical measurable-space and Borel-space instances on `E` and `M`

File-local canonical Borel structures, matching those in the other `Measure` files.
Declared `local` so they do not pollute external typeclass search. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Clean signature: explicit derivative form of the volume variation formula

Below, we package the general volume variation formula into an explicit form
where the derivative of `t ↦ ∫ f t d(μ_t)` is exhibited as the integral of
`(∂_t f + ½ · tr_g(∂_t g) · f)` against the (Riemannian volume) measure at the
base time. The derivation proceeds through three reusable lemmas:

1. A pointwise product-rule `HasDerivAt` for the chart-local integrand
   `s ↦ f s x · ρ_α x · density_α(gFam s, x)`, expressing the derivative in
   terms of `deriv (f · x) t`, `ρ_α x`, the density, and
   `traceTimeDerivMetric gFam t x`.
2. A per-chart variant `per_chart_integrand_hasDerivAt` isolating the
   pointwise derivative on the chart base set.
3. The clean global theorem `volume_variation_formula_clean`, which
   exhibits the global derivative integrand explicitly. -/

section CleanVolumeVariation

variable {g_fam : ℝ → SmoothRiemannianMetric I M}


section TraceTimeDerivMetricContinuous


end TraceTimeDerivMetricContinuous

/-! ## The per-chart parametric HasDerivAt lemma

Assembly of `hasDerivAt_setIntegral_model` and `per_chart_integrand_hasDerivAt`
into the single per-chart HasDerivAt needed to apply
`volume_variation_formula_clean_of_chart_derivs`. -/

section PerChartHasDerivAt

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

private lemma chartDensity_nonneg_of_base
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartDensity (I := I) g α x := by
  unfold chartDensity
  exact Real.sqrt_nonneg _


end PerChartHasDerivAt

/-! ## The clean volume variation formula -/

section CleanTheorem

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

/-- **Clean volume variation formula.** The time derivative of
`t ↦ ∫ f t d(vol_t)` along a regular family `g_fam` of Riemannian metrics and a
regular integrand `f : ℝ → M → ℝ`, at a base time `t₀`, equals the integral of
`∂_t f + ½ tr_g(∂_t g) · f` against the Riemannian volume measure at `t₀`.

Hypotheses: compact σ-compact Hausdorff manifold `M`, a regularity
interface `MetricFamilyRegularAt g_fam t₀` for the metric family, and a
regularity interface `FunctionRegularAt f t₀` for the integrand. -/
theorem volume_variation_formula_clean
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ := by
  -- Joint continuity of f.
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  -- Continuity of `f s` for every `s`.
  have hf_cont : ∀ᶠ s in 𝓝 t₀, Continuous (f s) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  -- Continuity of `f t₀`.
  have hft₀_cont : Continuous (f t₀) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t₀, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  -- Continuity of `deriv (f · x) t₀` in `x`.
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t₀) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t₀, x))) :=
      hf.continuous_deriv_joint.comp (continuous_const.prodMk continuous_id)
    exact this
  -- Continuity of the RHS integrand.
  have hh_cont : Continuous (fun x : M =>
      deriv (fun s : ℝ => f s x) t₀ +
      (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x) := by
    refine Continuous.add h_deriv_cont ?_
    refine Continuous.mul ?_ hft₀_cont
    refine Continuous.mul continuous_const ?_
    exact traceTimeDerivMetric_continuous (I := I) (M := M) hg
  -- Apply the clean-of-chart-derivs helper, providing per-chart HasDerivAt.
  refine volume_variation_formula_clean_of_chart_derivs
    (I := I) (M := M) g_fam f t₀ hf_cont hh_cont ?_
  intro α hα
  exact per_chart_hasDerivAt (I := I) (M := M) hg hf α hα

end CleanTheorem

end CleanVolumeVariation

end DifferentialGeometry.Integral.Measure
