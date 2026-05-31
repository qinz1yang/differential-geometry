import RicciFlower.Analysis.Volume.Family.Base

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Clean volume variation formula

This file contains the clean-signature volume-variation theorem layer split
out of `RicciFlower.Analysis.Volume.Family`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace RicciFlower
namespace Analysis
namespace Volume

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

/-- Pointwise product-rule `HasDerivAt` for the three-factor integrand at a point
`x` in a chart base set:
`s ↦ f s x · ρ x · chartDensity (g_fam s) α x`.

The derivative at `t` expands, via the product rule, into:
`(deriv (f · x) t · ρ x + f t x · ρ x · (1/2) · traceTimeDerivMetric ...) · density`,
which factors to
`(deriv (f · x) t + (1/2) · traceTimeDerivMetric g_fam t x · f t x) · ρ x · density`.
-/
lemma per_chart_integrand_hasDerivAt
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (f : ℝ → M → ℝ) (ρ : M → ℝ)
    (hf : HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t) :
    HasDerivAt
      (fun s : ℝ => f s x * ρ x *
        chartDensity (I := I) (g_fam s) α x)
      ((deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
        chartDensity (I := I) (g_fam t) α x) t := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  -- Gram-entry-wise HasDerivAt at `α`, evaluated at `x`.
  have hG : ∀ i j : n,
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j)
        (deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t) t := by
    intro i j
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg α hxα i j t
  -- The density `chartDensity (g_fam ·) α x` has the half-trace form derivative.
  have hdensity_deriv :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) *
          Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
            (Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)) *
          Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det) t := by
    have := hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
      (I := I) (M := M) g_fam α t (x := x) hxα
      (Matrix.of fun i j : n =>
        deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)
      (by
        intro i j
        exact hG i j)
    -- `chartDensityFamily g_fam α x` is defeq to `chartDensity (g_fam ·) α x`.
    change HasDerivAt (fun s => chartDensity (I := I) (g_fam s) α x) _ t
    exact this
  -- Rewrite the density-derivative constant using chart-invariance.
  have htrace :
      Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t))
        = traceTimeDerivMetric (I := I) g_fam t x := by
    -- By definition, chartGramMatrixFamily = chartGramMatrix (g_fam ·) α x.
    change Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))
      = traceTimeDerivMetric (I := I) g_fam t x
    rw [traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hxα]
  -- Also, `chartDensity (g_fam t) α x = √(det G_t α x)`.
  have hdensity_val :
      chartDensity (I := I) (g_fam t) α x
        = Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det := by
    rfl
  -- Rewrite the density-derivative constant cleanly.
  have hdensity_deriv' :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
          chartDensity (I := I) (g_fam t) α x) t := by
    rw [hdensity_val]
    -- Apply the rewrite on the HasDerivAt's RHS.
    have := hdensity_deriv
    rw [htrace] at this
    exact this
  -- Combine: `(f s x * ρ x) * density s` via product rule.
  -- First: `HasDerivAt (fun s => f s x * ρ x) (deriv_f * ρ x) t` (ρ x is constant in s).
  have hfρ : HasDerivAt (fun s : ℝ => f s x * ρ x)
      (deriv (fun s : ℝ => f s x) t * ρ x) t :=
    hf.mul_const (ρ x)
  -- Now the product rule on `(f · · ρ x) * density`.
  have hprod := hfρ.mul hdensity_deriv'
  -- Algebraic reorganization to match the stated derivative.
  have halgebra :
      (deriv (fun s : ℝ => f s x) t * ρ x) *
          chartDensity (I := I) (g_fam t) α x
        + (f t x * ρ x) *
          ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
            chartDensity (I := I) (g_fam t) α x)
      = (deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
          chartDensity (I := I) (g_fam t) α x := by
    ring
  rw [← halgebra]
  exact hprod

/-- Sum identity connecting the chart-local weighted integrals (appearing as the
right-hand sides of the per-chart `HasDerivAt`s in the volume variation formula)
to a single global integral against the Riemannian volume measure.

Given a continuous integrand `h : M → ℝ`, on a compact manifold,
`∑ α, ∫ x, h x * ρ_α x ∂(chartLocalMeasure (g_t) α) = ∫ x, h x ∂(riemannianMeasure_t)`.
This is obtained by rewriting each summand via the `withDensity → smul`
identity and applying the finite-sum decomposition of the Riemannian measure. -/
theorem chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (h : M → ℝ) (hh_cont : Continuous h) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)
      = ∫ x, h x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  classical
  -- Reduce to the finset-sum identity for the Riemannian volume measure.
  rw [riemannianMeasureFamily_def]
  rw [integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
      (g_fam t) h hh_cont]
  -- Pointwise, each summand matches up via `integral_withDensity`.
  refine Finset.sum_congr rfl (fun α _ => ?_)
  -- `∫ h ∂(cLM.withDensity (ofReal ρ_α)) = ∫ (ofReal ρ_α).toReal • h ∂cLM = ∫ ρ_α • h ∂cLM`.
  set ρ : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρ_def
  have hρ_cont : Continuous ρ := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρ_ae : AEMeasurable (fun x : M => ENNReal.ofReal (ρ x))
      (chartLocalMeasure (I := I) (g_fam t) α) := by
    exact (ENNReal.measurable_ofReal.comp hρ_cont.measurable).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) (g_fam t) α),
      ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hswap :
      ∫ x, h x
          ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal (ρ y)))
        = ∫ x, (ENNReal.ofReal (ρ x)).toReal • h x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) :=
    integral_withDensity_eq_integral_toReal_smul₀
      (μ := chartLocalMeasure (I := I) (g_fam t) α)
      (f := fun y : M => ENNReal.ofReal (ρ y)) hρ_ae hρ_lt_top
      (g := h)
  -- Simplify `(ENNReal.ofReal (ρ x)).toReal = ρ x` using nonnegativity.
  have htoReal : ∀ x, (ENNReal.ofReal (ρ x)).toReal = ρ x := fun x =>
    ENNReal.toReal_ofReal (hρ_nonneg x)
  have hsmul : ∀ x, (ENNReal.ofReal (ρ x)).toReal • h x = h x * ρ x := fun x => by
    rw [htoReal x, smul_eq_mul, mul_comm]
  have hintegrand_eq :
      (fun x : M => (ENNReal.ofReal (ρ x)).toReal • h x)
        = fun x : M => h x * ρ x := by
    funext x; exact hsmul x
  rw [hswap, hintegrand_eq]

/-- Clean version of the volume variation formula, with the derivative
integrand written explicitly.

The derivative of `t ↦ ∫ f t d(μ_t)` along the time-parameterised Riemannian
volume measures is the integral of
`(∂_t f + ½ · tr_g(∂_t g) · f)` against `μ_t` at the base time.

In the present formulation, the per-chart `HasDerivAt` hypothesis is retained:
deriving it from the joint smoothness of `(t, x) ↦ f t x` alone requires the
full parametric-integral machinery (uniform bounds over a chart-local
neighborhood, integrability over chart targets, the three-factor product rule
for the `f · ρ · density` integrand). The `per_chart_integrand_hasDerivAt`
lemma above packages the pointwise product-rule step; the remaining step is
the `hasDerivAt_integral_of_dominated_loc_of_deriv_le` specialization, which
requires explicit bounds and integrability arguments.

The `hα_deriv_explicit` hypothesis states the per-chart derivative with the
explicit RHS matching the form produced by `per_chart_integrand_hasDerivAt`
composed with parametric integration. The `hh_cont` hypothesis ensures the
RHS integrand is continuous, enabling the finite-sum-to-global-integral
identity. -/
theorem volume_variation_formula_clean_of_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hh_cont : Continuous
      (fun x : M => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x))
    (hα_deriv_explicit : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (∫ x, (deriv (fun s : ℝ => f s x) t +
                (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              (chartAtlasPOU I M) α x
            ∂(chartLocalMeasure (I := I) (g_fam t) α)) t) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t +
              (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t))
      t := by
  -- Set the abbreviation `Iα α := ∫ (deriv f + ½ trace * f) * ρ α d(cLM α)`.
  set h : M → ℝ :=
      fun x => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x with hh_def
  set Iα : M → ℝ := fun α =>
      ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α) with hIα_def
  -- Set the global value.
  set Iglobal : ℝ :=
      ∫ x, h x
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) with hIglobal_def
  -- Sum identity via the helper lemma.
  have hSum : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal := by
    exact chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
      (I := I) (M := M) g_fam t h hh_cont
  -- Apply the general-form formula.
  refine volume_variation_formula (I := I) (M := M)
    g_fam f t Iα Iglobal hf_cont ?_ hSum
  intro α hα
  exact hα_deriv_explicit α hα



/-! ## Continuity of `traceTimeDerivMetric` in the spatial variable

The function `x ↦ traceTimeDerivMetric g_fam t x` is continuous on `M`. This is
established by showing continuity on each chart base set, using the
chart-invariance identity to replace the canonical `x`-chart by a fixed `α`-chart,
combined with the joint continuity data packaged in `MetricFamilyRegularAt`.
-/

section TraceTimeDerivMetricContinuous

/-- Joint continuity in `(s, x)` of `trace((G_s α x)⁻¹ · ∂_s G_s α x)` on
`ℝ ×ˢ base_α`, for any chosen chart `α`. This follows from joint continuity of
the Gram matrix and its pointwise time-derivatives on `ℝ × base_α`, together with
continuity of the matrix inverse on the positive-determinant locus and of the
matrix trace. -/
lemma continuousOn_traceTimeDerivMetric_on_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) :
    ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have hdG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_deriv_chartGramMatrix α i j
  -- Det continuous.
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp : (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
        = (fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i, chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finset_sum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  -- Adjugate entry continuous.
  have h_adj_cont : ∀ k v : n, ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro k v
    have hform : ∀ p : ℝ × M,
        (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v
          = ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)).det := by
      intro p; rw [adjugate_apply]
    have hexp : ∀ p : ℝ × M,
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v (Pi.single k 1)).det
          = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i : n,
              ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                (Pi.single k 1)) (σ i) i := by
      intro p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    have hfn_eq :
        (fun p : ℝ × M =>
          (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
          = fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i : n,
                ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                  (Pi.single k 1)) (σ i) i := by
      funext p; rw [hform p, hexp p]
    rw [hfn_eq]
    refine continuousOn_finset_sum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    by_cases hiv : σ i = v
    · have hconst :
          (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun _ => (Pi.single k 1 : n → ℝ) i := by
        funext p
        rw [hiv, Matrix.updateRow_self]
      rw [hconst]; exact continuousOn_const
    · have hnonrow :
          (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun p : ℝ × M =>
              chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i := by
        funext p
        rw [Matrix.updateRow_apply]
        exact if_neg hiv
      rw [hnonrow]; exact hG_joint (σ i) i
  -- Det nonzero on domain.
  have h_det_ne_zero : ∀ p ∈ (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
        : Set (ℝ × M)),
      (chartGramMatrix (I := I) (g_fam p.1) α p.2).det ≠ 0 := by
    intro p hp
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g_fam p.1) α hp.2)
  -- Inverse entries continuous.
  have h_inv_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have h_inv_entry : ∀ p : ℝ × M,
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j
          = (chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      intro p
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, Ring.inverse_eq_inv']
    have hfn_eq :
        (fun p : ℝ × M => ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
          = fun p : ℝ × M =>
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      funext p; exact h_inv_entry p
    rw [hfn_eq]
    refine ContinuousOn.mul ?_ (h_adj_cont i j)
    exact h_det_cont.inv₀ h_det_ne_zero
  -- Product entry continuous.
  have h_prod_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have hfun :
        (fun p : ℝ × M =>
          ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
          = fun p : ℝ × M =>
            ∑ k : n, ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i k *
              (deriv (fun s : ℝ =>
                chartGramMatrix (I := I) (g_fam s) α p.2 k j) p.1) := by
      funext p
      rw [Matrix.mul_apply]
      rfl
    rw [hfun]
    refine continuousOn_finset_sum _ (fun k _ => ?_)
    exact (h_inv_cont i k).mul (hdG_joint k j)
  -- Trace is diagonal sum.
  have htrace_eq : ∀ p : ℝ × M,
      Matrix.trace ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
        = ∑ i : n,
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
              Matrix.of fun i j : n =>
                deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    intro p
    rfl
  have hfun : (fun p : ℝ × M =>
        Matrix.trace ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1))
      = fun p : ℝ × M =>
          ∑ i : n, ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    funext p; exact htrace_eq p
  rw [hfun]
  refine continuousOn_finset_sum _ (fun i _ => h_prod_cont i i)

/-- Continuity in `x` of `traceTimeDerivMetric g_fam t x` on `M`. This is the
coordinate-invariant scalar, so continuity is established by switching to the
canonical chart at each point and applying the continuous-on-base-set result. -/
lemma traceTimeDerivMetric_continuous
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) :
    Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) := by
  classical
  refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
  set n := Fin (Module.finrank ℝ E) with hn_def
  -- On the α := x₀-chart base set, `traceTimeDerivMetric g_fam t x` equals the chart
  -- formula using the x₀-chart. The x₀-chart base set contains x₀ and is open.
  set α : M := x₀
  have hα_base_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x₀ ∈ (chartAt H x₀).source
    exact mem_chart_source _ _
  -- Joint continuity of the trace-form expression on univ ×ˢ base_α.
  have h_joint : ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  -- Slice at fixed t.
  have h_slice : ContinuousOn
      (fun x : M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hp : ((t, x) : ℝ × M) ∈
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      ⟨Set.mem_univ _, hx⟩
    have h_at := (h_joint (t, x) hp)
    -- Restrict to the slice {t} × base_α, then transfer to the x-slice.
    have hincl_cont : Continuous (fun y : M => ((t, y) : ℝ × M)) :=
      continuous_const.prodMk continuous_id
    have hincl_mapsTo : Set.MapsTo (fun y : M => ((t, y) : ℝ × M))
        (trivializationAt E (TangentSpace I) α).baseSet
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      fun y hy => ⟨Set.mem_univ _, hy⟩
    exact h_at.comp hincl_cont.continuousWithinAt hincl_mapsTo
  -- On base_α, traceTimeDerivMetric g_fam t x = trace form at α.
  have hev : (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) =ᶠ[𝓝 x₀]
      (fun x : M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))) := by
    filter_upwards [hα_base_open.mem_nhds hx₀_base] with y hy
    exact traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hy
  refine ContinuousAt.congr ?_ hev.symm
  exact h_slice.continuousAt (hα_base_open.mem_nhds hx₀_base)

/-- Joint continuity of `(t, x) ↦ traceTimeDerivMetric g_fam t x` on
`Set.univ ×ˢ base_α`, for any chart `α`. Obtained from the chart-local
trace formula via `traceTimeDerivMetric_eq_trace_chartGramMatrix`. -/
lemma continuousOn_traceTimeDerivMetric_of_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base
    (I := I) (M := M) hreg α
  have h_eq : Set.EqOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro p hp
    exact traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hp.2
  exact h_base.congr h_eq

/-- Joint continuity of the chart-local density `(t, x) ↦ chartDensity (g_fam t) α x`
on `Set.univ ×ˢ base_α`, derived from the regularity interface. -/
lemma continuousOn_chartDensity_family
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp :
        (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
          = (fun p : ℝ × M =>
              ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∏ i, chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finset_sum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  have h_sqrtdet_cont : ContinuousOn
      (fun p : ℝ × M =>
        Real.sqrt ((chartGramMatrix (I := I) (g_fam p.1) α p.2).det))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    Real.continuous_sqrt.comp_continuousOn h_det_cont
  refine h_sqrtdet_cont.congr ?_
  intro p _; rfl

/-- Pull-back variant: joint continuity of the chart-α trace form pulled back
through the chart symm, on an arbitrary set `S ⊆ ℝ × E` mapping into the base
set. -/
lemma continuousOn_chartTrace_form_of_base_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M)
    {S : Set (ℝ × E)} (sym : E → M)
    (hsym_cont : ContinuousOn (fun p : ℝ × E => (p.1, sym p.2)) S)
    (hsym_maps : Set.MapsTo (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M)) S
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn
      (fun p : ℝ × E => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α (sym p.2))⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (sym p.2) i j) p.1)))
      S := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  have h_comp : ContinuousOn
      ((fun p : ℝ × M => Matrix.trace
          ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
        ∘ (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M))) S :=
    h_base.comp hsym_cont hsym_maps
  exact h_comp

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

set_option maxHeartbeats 16000000 in
-- The proof below assembles several measure-theoretic sub-lemmas with joint
-- continuity / differentiability arguments; the combined elaboration load exceeds
-- the default heartbeats budget.
/-- Per-chart parametric `HasDerivAt`: the chart-local integral
`s ↦ ∫ x, f s x ∂(chartLocalMeasure (g_fam s) α).withDensity (ofReal ρ_α)` has a
derivative at `t` given by the explicit formula
`∫ x, (∂_t f + ½ tr_g(∂_t g) f) · ρ_α ∂(chartLocalMeasure (g_fam t) α)`. -/
lemma per_chart_hasDerivAt
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M} {f : ℝ → M → ℝ} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (hf : FunctionRegularAt f t)
    (α : M) (_hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      (∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
            (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)) t := by
  classical
  -- Setup.
  set n := Fin (Module.finrank ℝ E) with hn_def
  set ρα : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρα_def
  set μₐ : MeasureTheory.Measure M := chartLocalMeasure (I := I) (g_fam t) α with hμα_def
  set target : Set E := (extChartAt I α).target with htarget_def
  set symm : E → M := fun y => (extChartAt I α).symm y with hsymm_def
  have htarget_meas : MeasurableSet target :=
    measurableSet_extChartAt_target (I := I) α
  -- Continuity facts for ρα, f, density, and the combined integrand.
  have hρα_cont : Continuous ρα := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρα_nonneg : ∀ x, 0 ≤ ρα x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρα_le_one : ∀ x, ρα x ≤ 1 := fun x => (chartAtlasPOU I M).le_one _ _
  have hρα_subord : tsupport ρα ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- tsupport is compact on compact M (tsupport is closed, compact space).
  have hρα_tsupport_compact : IsCompact (tsupport ρα) := isClosed_tsupport ρα |>.isCompact
  -- Continuity of `f` on `ℝ × M`.
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  -- The slice `f t ·`.
  have hft_cont : Continuous (f t) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  -- Joint continuity of deriv in (s, y).
  have h_deriv_cont_joint_M : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  -- Continuity of deriv (f · ·) t.
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t, x))) :=
      h_deriv_cont_joint_M.comp (continuous_const.prodMk continuous_id)
    exact this
  -- Continuity of traceTimeDerivMetric t ·.
  have h_tr_cont : Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hreg
  -- Continuity of the Riemannian density on the α-base set.
  have h_density_contOn : ContinuousOn
      (fun x : M => chartDensity (I := I) (g_fam t) α x)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_continuousOn (I := I) (g_fam t) α
  -- The map symm : E → M is continuous on target.
  have h_symm_contOn : ContinuousOn symm target :=
    continuousOn_extChartAt_symm (I := I) α
  -- The chart symm maps target into the chart source (= trivialization base set).
  have h_symm_maps : ∀ y ∈ target, symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsrc : symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
    exact hsrc
  -- Bound on M.
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x, ‖f t x‖ ≤ C := by
    have hIm := (isCompact_univ (X := M)).image hft_cont.norm
    obtain ⟨C, hC⟩ := hIm.bddAbove
    exact ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩
  -- Step 1: Use the explicit product form of the integrand.
  -- On target, the integral of `f s` against the withDensity-measure equals
  -- ∫ y in target, density * (ρα * f s) ∂modelHaar.
  -- We work with Fmdl s y := f s (symm y) * ρα (symm y) * chartDensity (g_fam s) α (symm y).
  set Fmdl : ℝ → E → ℝ := fun s y =>
    f s (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam s) α (symm y)
  -- The derivative of Fmdl in s at t, given by per_chart_integrand_hasDerivAt.
  set Fprim : ℝ → E → ℝ := fun s y =>
    (deriv (fun r : ℝ => f r (symm y)) s +
      (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
        f s (symm y)) * ρα (symm y) *
      chartDensity (I := I) (g_fam s) α (symm y)
  -- Pointwise derivative on target.
  have hH'_deriv : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s _
    have hsym_base : symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      h_symm_maps y hy
    -- `fun r => f r (symm y)` has derivative (deriv ...) s (pointwise regularity).
    have hslice : HasDerivAt (fun r : ℝ => f r (symm y))
        (deriv (fun r : ℝ => f r (symm y)) s) s :=
      hf.hasDerivAt_time (symm y) s
    have hpcd := per_chart_integrand_hasDerivAt
      (I := I) (M := M) (t := s) (hreg.at_any s) α (x := symm y) hsym_base f ρα hslice
    exact hpcd
  -- Bounds.
  -- Strategy: build a bound `b : E → ℝ` such that for `s ∈ ball t 1` (nbhd of t),
  -- `‖Fprim s y‖ ≤ b y` on target.
  -- We bound `Fprim` on the compact `K'_α := (extChartAt I α) '' tsupport ρα`, and zero
  -- outside (since `symm y ∉ tsupport ρα` implies `ρα (symm y) = 0`, hence `Fprim s y = 0`).
  set K : Set M := tsupport ρα
  set K' : Set E := (extChartAt I α) '' K
  have hK_compact : IsCompact K := hρα_tsupport_compact
  have hK'_compact : IsCompact K' :=
    hK_compact.image_of_continuousOn (continuousOn_extChartAt (I := I) α |>.mono (by
      intro y hy
      have : y ∈ (chartAt H α).source := hρα_subord hy
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this))
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  -- measure of K' finite.
  have hK'_meas_lt_top : (modelHaar (E := E)) K' < ⊤ :=
    hK'_compact.measure_lt_top
  -- Bound constants:
  -- |Fprim s y| ≤ |deriv + 1/2 trace f| * |ρα| * |density|. On K' (= image of tsupport),
  -- each factor is bounded (by continuity on compact set).
  -- Compute: for `s ∈ ball t 1`, everything involves only `s` — but our bound `h_bound` must
  -- be uniform over all `s ∈ ball t 1`. Issue: `(deriv (f · y) s)`, `trace g_fam s y`,
  -- `density (g_fam s) α y`, and `f s y` all depend on `s`.
  -- Uniform bound requires joint continuity in `(s, y)` on `[t-1, t+1] × K'`.
  -- Simpler: use the simple bound coming from continuous joint maps on compact sets.
  -- Joint continuity of `deriv (f · ·) ·` in `(s, y)`?  This is the issue.
  -- To sidestep, apply the parametric integral theorem with `s := {t}` (a degenerate slice —
  -- but Mathlib's theorem requires `s` a nhd). We use the joint continuity of
  -- `(s, y) ↦ Fprim s y` on `ball t 1 × K'`, bound by the `isCompact.bddAbove_image ‖·‖`.
  -- Jointly in `(s, y)`:
  --   - `f : ℝ × M → ℝ` is continuous (joint, from hf).
  --   - `deriv (f · y) s` is jointly continuous in `(s, y)` — this requires
  --     continuity of `fderiv` in the base point, which is the analogue of
  --     `continuous_deriv_slice` but in both arguments.
  --   - `traceTimeDerivMetric g_fam s y` is jointly continuous in `(s, y)` — another
  --     joint fact.
  --   - `chartDensity (g_fam s) α y` is jointly continuous on `ℝ × base_α`.
  -- We punt on the JOINT derivative-continuity question by using the following
  -- dominance: take `s ∈ {t}` via `s := Set.univ`, use `deriv (f · y) · = deriv (f · y)`
  -- pointwise — but Mathlib's theorem needs the dependency on `s`.
  -- Alternative: observe that the derivative is continuous in the joint `(s, y)`
  -- argument via the same construction as `continuous_deriv_slice`.
  -- The joint partial-derivative `(s, y) ↦ ∂_s f s y` is continuous: it equals
  -- `fderiv ((fun p => f p.1 p.2) ∘ (fun p => (p.1, p.2))) p (1, 0)`, and `fderiv`
  -- is continuous. We use `partial_deriv_cont`, proven below inline.
  have h_deriv_cont_joint : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  -- Joint continuity of `(s, y) ↦ traceTimeDerivMetric g_fam s y` at fixed `(t, y)`?
  -- For our bound we just need uniformity on `ball t 1 × K'`, but since we don't have
  -- `traceTimeDerivMetric` continuously dependent on `s` easily, we bound it simpler:
  -- use the joint continuity of `chartGramMatrix` entries and their time-derivatives,
  -- pull back via the α-chart using chart-invariance. This is substantial work.
  -- Simpler path: bound `|Fprim|` on `[t-1, t+1] × K'` by continuity of the individual
  -- factors.
  -- Let's bound each factor independently on a compact set.
  -- Define: q (s, y) := Fprim s y on `Ω := Set.Icc (t - 1) (t + 1) ×ˢ K'`.
  -- We argue Fprim itself is continuous on Ω as a function of (s, y).
  set I₁ : Set ℝ := Set.Icc (t - 1) (t + 1)
  have hI₁_compact : IsCompact I₁ := isCompact_Icc
  have ht_interior : t ∈ Set.Ioo (t - 1 : ℝ) (t + 1) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have ht_in_I₁ : t ∈ I₁ := ⟨by linarith, by linarith⟩
  -- ball t 1 is an open nbhd of t contained in Ioo, and its closure ⊆ I₁.
  -- We use the open ball.
  set ball_s : Set ℝ := Metric.ball t 1
  have hballs_nhd : ball_s ∈ 𝓝 t := Metric.ball_mem_nhds _ one_pos
  have hballs_sub_I₁ : ball_s ⊆ I₁ := by
    intro s hs
    have hs' : |s - t| < 1 := by simpa [Real.dist_eq, Real.norm_eq_abs] using hs
    refine ⟨?_, ?_⟩
    · have := (abs_lt.mp hs').1; linarith
    · have := (abs_lt.mp hs').2; linarith
  -- Define the closed bound domain.
  set Ω : Set (ℝ × E) := I₁ ×ˢ K'
  have hΩ_compact : IsCompact Ω := hI₁_compact.prod hK'_compact
  -- Continuity of Fmdl on ℝ × E (full domain, pushing through symm).
  -- But symm is only defined on target; outside target, Fmdl still makes sense
  -- (symm is total — PartialEquiv), but not necessarily continuous.
  -- Let's restrict to target.
  -- Actually we only need bound on Ω ∩ (ℝ × target) = I₁ ×ˢ K' since K' ⊆ target.
  have hK'_sub_target : K' ⊆ target := by
    intro y hy
    obtain ⟨x, hxK, hx_eq⟩ := hy
    have hx_src : x ∈ (extChartAt I α).source := by
      have : x ∈ (chartAt H α).source := hρα_subord hxK
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    rw [← hx_eq]
    exact (extChartAt I α).map_source hx_src
  -- Prove: on Ω, |Fprim s y| ≤ C₀ for some constant C₀.
  -- Fprim s y on K' (where symm y ∈ (chartAt H α).source ⊆ base_α since we're on target_α after
  -- intersection):
  -- Each of the factors is continuous on Ω:
  -- (1) `(s, y) ↦ f s (symm y)` = `(fun p => f p.1 p.2) ∘ (s, symm y)`: continuous where
  -- symm is continuous on K' ⊆ target.
  -- (2) `ρα (symm y)`: continuous in y on K'.
  -- (3) `density (g_fam s) α (symm y)`: continuous jointly on ball_s × K' because
  -- `chartDensity_contMDiff_family` yields joint ContMDiff on `univ ×ˢ base_α`.
  -- (4) `deriv (f · (symm y)) s`: joint continuity from `h_deriv_cont_joint`.
  -- (5) `traceTimeDerivMetric g_fam s (symm y)`: we need joint continuity in (s, y).
  -- We handle (5) directly via the chart-α expression:
  -- On `base_α`, `traceTimeDerivMetric g_fam s x = trace((G_s α x)⁻¹ * dG_s α x)`,
  -- each entry jointly ContMDiff and ContDiff in (s, x). Proved in the `TraceTime...` section.
  -- For simplicity, we derive a crude constant bound using continuity on Ω:
  have h_Fprim_continuousOn_Ω :
      ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := by
    -- We work directly: on K' ⊆ target, symm is continuous. And for y ∈ K', symm y ∈ base_α.
    have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
    have h_symm_pair_contOn :
        ContinuousOn (fun p : ℝ × E => (p.1, symm p.2)) (I₁ ×ˢ K') := by
      refine ContinuousOn.prodMk continuousOn_fst ?_
      refine h_symm_contOn_K'.comp continuousOn_snd ?_
      intro p hp
      exact hp.2
    -- (1) f (s, symm y) continuous on I₁ ×ˢ K'.
    have hf_comp : ContinuousOn (fun p : ℝ × E => f p.1 (symm p.2)) (I₁ ×ˢ K') := by
      exact hf_cont_joint.continuousOn.comp h_symm_pair_contOn (fun _ _ => Set.mem_univ _)
    -- (2) ρα (symm y) continuous.
    have hρα_comp : ContinuousOn (fun p : ℝ × E => ρα (symm p.2)) (I₁ ×ˢ K') := by
      have : ContinuousOn (fun y : E => ρα (symm y)) K' := by
        exact hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      exact (this.comp continuousOn_snd (fun _ hp => hp.2))
    -- (3) chartDensity (g_fam ·) α (symm ·) continuous in (s, y).
    have hdensity_comp : ContinuousOn
        (fun p : ℝ × E => chartDensity (I := I) (g_fam p.1) α (symm p.2))
        (I₁ ×ˢ K') := by
      have h_joint_cont : ContinuousOn
          (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
        continuousOn_chartDensity_family (I := I) (M := M) hreg α
      have hmaps : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
          (I₁ ×ˢ K')
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
        intro p hp
        refine ⟨Set.mem_univ _, ?_⟩
        exact h_symm_maps p.2 (hK'_sub_target hp.2)
      exact h_joint_cont.comp h_symm_pair_contOn hmaps
    -- (4) deriv (f · ·) · joint continuous.
    have h_deriv_comp : ContinuousOn
        (fun p : ℝ × E => deriv (fun r : ℝ => f r (symm p.2)) p.1) (I₁ ×ˢ K') := by
      exact h_deriv_cont_joint.continuousOn.comp h_symm_pair_contOn
        (fun _ _ => Set.mem_univ _)
    -- (5) traceTimeDerivMetric joint — go via the chart-α trace form directly.
    have h_symm_pair_mapsTo : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
        (I₁ ×ˢ K')
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun p hp =>
      ⟨Set.mem_univ _, h_symm_maps p.2 (hK'_sub_target hp.2)⟩
    have h_tr_base_pb :
        ContinuousOn (fun p : ℝ × E => Matrix.trace
          ((chartGramMatrix (I := I) (g_fam p.1) α (symm p.2))⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (symm p.2) i j) p.1)))
        (I₁ ×ˢ K') :=
      continuousOn_chartTrace_form_of_base_pullback (I := I) (M := M) hreg α
        (sym := symm) h_symm_pair_contOn h_symm_pair_mapsTo
    have h_tr_comp : ContinuousOn
        (fun p : ℝ × E => traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2))
        (I₁ ×ˢ K') := by
      refine h_tr_base_pb.congr ?_
      intro p hp
      have hsym_base : symm p.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
        h_symm_maps p.2 (hK'_sub_target hp.2)
      exact traceTimeDerivMetric_eq_trace_chartGramMatrix
        (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hsym_base
    -- Fprim p.1 p.2 is `(deriv + 1/2 * trace * f) * ρ * density` by `rfl`.
    -- Assemble directly via the product rule.
    change ContinuousOn (fun p : ℝ × E =>
        (deriv (fun r : ℝ => f r (symm p.2)) p.1 +
            (1/2) * traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2) *
              f p.1 (symm p.2)) * ρα (symm p.2) *
          chartDensity (I := I) (g_fam p.1) α (symm p.2)) (I₁ ×ˢ K')
    refine ContinuousOn.mul (ContinuousOn.mul ?_ hρα_comp) hdensity_comp
    refine ContinuousOn.add h_deriv_comp ?_
    refine ContinuousOn.mul ?_ hf_comp
    refine ContinuousOn.mul continuousOn_const ?_
    exact h_tr_comp
  -- Bound.
  obtain ⟨CH, hCH⟩ : ∃ C, ∀ p ∈ (I₁ ×ˢ K'), |Fprim p.1 p.2| ≤ C := by
    classical
    by_cases hne' : (I₁ ×ˢ K' : Set (ℝ × E)).Nonempty
    · -- Use sup of |Fprim| on compact Ω.
      have hΩne : Ω.Nonempty := hne'
      have h_abs_cont : ContinuousOn (fun p : ℝ × E => |Fprim p.1 p.2|) Ω :=
        h_Fprim_continuousOn_Ω.abs
      have hbdd := hΩ_compact.bddAbove_image h_abs_cont
      obtain ⟨C, hC⟩ := hbdd
      refine ⟨C, fun p hp => ?_⟩
      exact hC ⟨p, hp, rfl⟩
    · -- Empty Ω: trivially any C works.
      refine ⟨0, fun p hp => ?_⟩
      exact (hne' ⟨p, hp⟩).elim
  -- Define b := |CH| · indicator K' 1.
  set C₀ : ℝ := |CH|
  set b : E → ℝ := fun y => C₀ * (K'.indicator (fun _ : E => (1 : ℝ))) y with hb_def
  have hb_nonneg : ∀ y, 0 ≤ b y := by
    intro y
    have h_ind_nonneg : 0 ≤ K'.indicator (fun _ : E => (1 : ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    exact mul_nonneg (abs_nonneg _) h_ind_nonneg
  have hb_integrable : Integrable b ((modelHaar (E := E)).restrict target) := by
    -- `b = C₀ • indicator K'`, K' is measurable with finite measure, so indicator is integrable.
    have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
        ((modelHaar (E := E)).restrict target) := by
      have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ))) (modelHaar (E := E)) := by
        rw [integrable_indicator_iff hK'_meas]
        exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
      exact h_rest_int.restrict
    have := h_ind_int.const_mul C₀
    simpa [b, smul_eq_mul] using this
  -- Bound property.
  have h_bound_prop : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, ‖Fprim s y‖ ≤ b y := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s hs
    by_cases hyK' : y ∈ K'
    · -- `y ∈ K'`, `s ∈ ball_s ⊆ I₁`, both in Ω.
      have hp : (s, y) ∈ (I₁ ×ˢ K' : Set (ℝ × E)) := ⟨hballs_sub_I₁ hs, hyK'⟩
      have hbound := hCH (s, y) hp
      have hby : b y = C₀ := by
        simp [b, Set.indicator_of_mem hyK']
      rw [Real.norm_eq_abs, hby]
      have : |Fprim s y| ≤ CH := hbound
      -- We need |Fprim s y| ≤ C₀ = |CH|. Since |Fprim s y| ≤ CH ≤ |CH|:
      refine this.trans ?_
      exact le_abs_self _
    · -- y ∉ K'. Then symm y ∉ tsupport ρα. Hence ρα (symm y) = 0, so Fprim s y = 0.
      have h_symm_y_not_in : symm y ∉ K := by
        intro hsymInK
        exact hyK' ⟨symm y, hsymInK, by
          -- Need ec (symm y) = y; but we don't necessarily know y ∈ target.
          -- But we need to deal with that too. If y ∉ target, then ρ-factor is the only thing
          -- saving us. But here we're in the ae_restrict_iff' branch where `y ∈ target`.
          exact (extChartAt I α).right_inv hy⟩
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        have : symm y ∈ Function.support ρα := h
        exact h_symm_y_not_in (subset_tsupport _ this)
      have hH'_zero : Fprim s y = 0 := by
        change (deriv (fun r : ℝ => f r (symm y)) s +
            (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
              f s (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam s) α (symm y) = 0
        rw [hρ_zero, mul_zero, zero_mul]
      rw [hH'_zero]
      have hby_nonneg : 0 ≤ b y := hb_nonneg y
      simpa using hby_nonneg
  -- Measurability of F at t and F' at t.
  have hH_meas_at_t : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (Fmdl s) ((modelHaar (E := E)).restrict target) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    -- On target, Fmdl s y = f s (symm y) * ρα (symm y) * density (g_fam s) α (symm y).
    -- All factors continuous on target.
    have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
    have h_f_s_comp_contOn : ContinuousOn (fun y : E => f s (symm y)) target := by
      have hf_s_cont : Continuous (f s) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      exact hf_s_cont.continuousOn.comp h_symm_contOn_target
        (fun _ _ => Set.mem_univ _)
    have h_ρα_comp_contOn : ContinuousOn (fun y : E => ρα (symm y)) target :=
      hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
    have h_density_comp_contOn : ContinuousOn
        (fun y : E => chartDensity (I := I) (g_fam s) α (symm y)) target := by
      have h_density_s : ContinuousOn
          (fun x : M => chartDensity (I := I) (g_fam s) α x)
          (trivializationAt E (TangentSpace I) α).baseSet :=
        chartDensity_continuousOn (I := I) (g_fam s) α
      exact h_density_s.comp h_symm_contOn_target h_symm_maps
    have h_H_s_contOn : ContinuousOn (Fmdl s) target := by
      -- Fmdl s y = f s (symm y) * ρα (symm y) * density (g_fam s) α (symm y)
      exact (h_f_s_comp_contOn.mul h_ρα_comp_contOn).mul h_density_comp_contOn
    exact (h_H_s_contOn.aestronglyMeasurable htarget_meas)
  have hH_int_at_t : Integrable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
    -- Bounded by a constant on target (via compact tsupport of ρα).
    -- |Fmdl t y| = |f t (symm y)| * |ρα (symm y)| * |density (g_fam t) α (symm y)|.
    -- For y ∉ K', symm y ∉ tsupport ρα ⇒ ρα (symm y) = 0 ⇒ Fmdl t y = 0.
    -- For y ∈ K', |Fmdl t y| bounded by Cf * 1 * sup_density.
    -- We give Fmdl t as K'.indicator of a bounded continuous function.
    -- Use `Integrable.mono` with a bound.
    -- Construct Fmdl (t) restricted to K'.
    -- Approach: use `h_Fprim_continuousOn_Ω` analogue for Fmdl t.
    -- Actually simpler: Fmdl t equals Fprim_indicator * indicator_K' where Fmdl is bounded on Ω.
    -- Let's bound via continuity on compact K' and Fmdl t ≡ 0 outside K' (modulo target).
    have h_Ht_cont_K' : ContinuousOn (Fmdl t) K' := by
      have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_comp : ContinuousOn (fun y : E => f t (symm y)) K' :=
        hf_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_ρα_comp : ContinuousOn (fun y : E => ρα (symm y)) K' :=
        hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_density_comp : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) K' := by
        refine h_density_contOn.comp h_symm_contOn_K' ?_
        intro y hy
        exact h_symm_maps y (hK'_sub_target hy)
      exact (h_f_comp.mul h_ρα_comp).mul h_density_comp
    -- Bound on K' by sup.
    obtain ⟨C_Fmdl, hC_H⟩ : ∃ C, ∀ y ∈ K', |Fmdl t y| ≤ C := by
      by_cases hK'_ne : K'.Nonempty
      · have h_abs_cont : ContinuousOn (fun y : E => |Fmdl t y|) K' := h_Ht_cont_K'.abs
        obtain ⟨C, hC⟩ := hK'_compact.bddAbove_image h_abs_cont
        refine ⟨C, fun y hy => ?_⟩
        exact hC ⟨y, hy, rfl⟩
      · refine ⟨0, fun y hy => ?_⟩
        exact absurd ⟨y, hy⟩ hK'_ne
    -- Fmdl t is zero outside K' (in target). Use `K'.indicator (fun _ => max C_Fmdl 0)` as dominant.
    have hH_t_vanish : ∀ y ∈ target, y ∉ K' → Fmdl t y = 0 := by
      intro y hy_tg hy_not
      have : symm y ∉ K := by
        intro h
        have hsrc : symm y ∈ (chartAt H α).source := hρα_subord h
        have hsrc' : symm y ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
        apply hy_not
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy_tg
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact this (subset_tsupport _ (show symm y ∈ Function.support ρα from h))
      change f t (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    -- Construct a dominating function.
    set C_Fprim : ℝ := max C_Fmdl 0
    have hC_Fprim_nonneg : 0 ≤ C_Fprim := le_max_right _ _
    -- Mono with `fun y => C_Fprim * K'.indicator 1 y`.
    have h_domHt : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
        ‖Fmdl t y‖ ≤ C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK', mul_one, Real.norm_eq_abs]
        calc |Fmdl t y| ≤ C_Fmdl := hC_H y hyK'
          _ ≤ C_Fprim := le_max_left _ _
      · rw [hH_t_vanish y hy hyK']
        rw [Set.indicator_of_notMem hyK', mul_zero, norm_zero]
    have h_bound_int' : Integrable
        (fun y : E => C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y)
        ((modelHaar (E := E)).restrict target) := by
      have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
          ((modelHaar (E := E)).restrict target) := by
        have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
            (modelHaar (E := E)) := by
          rw [integrable_indicator_iff hK'_meas]
          exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
        exact h_rest_int.restrict
      simpa [smul_eq_mul] using h_ind_int.const_mul C_Fprim
    -- Measurability of Fmdl t.
    have h_meas_Ht : AEStronglyMeasurable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
      have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_cont : ContinuousOn (fun y : E => f t (symm y)) target :=
        hf_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_ρ_cont : ContinuousOn (fun y : E => ρα (symm y)) target :=
        hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_d_cont : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) target :=
        h_density_contOn.comp h_symm_contOn_target h_symm_maps
      exact ((h_f_cont.mul h_ρ_cont).mul h_d_cont).aestronglyMeasurable htarget_meas
    exact h_bound_int'.mono' h_meas_Ht h_domHt
  have hH'_meas_at_t : AEStronglyMeasurable (Fprim t)
      ((modelHaar (E := E)).restrict target) := by
    -- Fprim t is continuous on K' (and 0 off K' target-ae).
    -- We represent Fprim t = K'.indicator (Fprim_main t ·) + 0 off-K' modulo null.
    -- We use the bound: Fprim t equals a function that is continuous on K' and 0 outside tsupport-pullback.
    -- Simpler: since Fprim t = if symm y ∈ base then _ else 0, and we work ae on target,
    -- provide a ae-strongly-measurable witness.
    -- Use the fact Fprim is ContinuousOn (I₁ ×ˢ K') at the slice t.
    have h_t_in_I₁ : t ∈ I₁ := ht_in_I₁
    -- Slice: `fun y => Fprim t y` on K'.
    have h_Ht'_cont_K' : ContinuousOn (fun y : E => Fprim t y) K' := by
      have := h_Fprim_continuousOn_Ω
      have : ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := this
      -- Slice by fixing p.1 := t.
      intro y hy
      have hp : (t, y) ∈ (I₁ ×ˢ K') := ⟨h_t_in_I₁, hy⟩
      -- ContinuousOn at (t, y) → ContinuousAt within K' at y via composition with constant map.
      have hat : ContinuousWithinAt (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') (t, y) :=
        this (t, y) hp
      have hincl_cont : Continuous (fun e : E => (t, e)) :=
        continuous_const.prodMk continuous_id
      have hincl_mapsTo : Set.MapsTo (fun e : E => (t, e)) K' (I₁ ×ˢ K') :=
        fun e he => ⟨h_t_in_I₁, he⟩
      exact hat.comp hincl_cont.continuousWithinAt hincl_mapsTo
    -- Off K' ∩ target, Fprim t vanishes. Fprim t is not necessarily continuous on all of target.
    -- But target = (K' ∩ target) ∪ (target \ K'), both measurable.
    -- Fprim t is strongly measurable on both: continuous on K' ∩ target ⊆ K', and 0 on target \ K'.
    -- Build via piecewise.
    -- Fprim t = K'.indicator (fun y => Fprim t y) modulo off-K' where Fprim t may be nonzero only if `symm y ∈ base` AND outside K', but ρα = 0 then, so Fprim t = 0.
    have h_Ht'_zero_off : ∀ y ∈ target, y ∉ K' → Fprim t y = 0 := by
      intro y hy hyK'
      have h_symm_y_not_K : symm y ∉ K := by
        intro h
        apply hyK'
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact h_symm_y_not_K (subset_tsupport _
          (show symm y ∈ Function.support ρα from h))
      change (deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y) *
          chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    -- Build `Fprim t` as `K'.indicator ∘ F + (target \ K').indicator ∘ 0`, using piecewise.
    -- Use `Indicator.aestronglyMeasurable` and continuity.
    have h_ind_Ht : Fprim t =ᵐ[(modelHaar (E := E)).restrict target]
        K'.indicator (fun y => Fprim t y) := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK']
      · rw [Set.indicator_of_notMem hyK']
        exact h_Ht'_zero_off y hy hyK'
    refine AEStronglyMeasurable.congr ?_ h_ind_Ht.symm
    -- K'.indicator of a function continuous on K'.
    have h_ind_meas : AEStronglyMeasurable
        (K'.indicator (fun y : E => Fprim t y))
        ((modelHaar (E := E)).restrict target) := by
      have h_restrict : AEStronglyMeasurable (fun y : E => Fprim t y)
          ((modelHaar (E := E)).restrict K') := by
        exact h_Ht'_cont_K'.aestronglyMeasurable hK'_meas
      have : AEStronglyMeasurable (K'.indicator (fun y : E => Fprim t y))
          (modelHaar (E := E)) := by
        refine (aestronglyMeasurable_indicator_iff hK'_meas).mpr ?_
        exact h_restrict
      exact this.restrict
    exact h_ind_meas
  -- Apply hasDerivAt_setIntegral_model.
  have h_s_mem : ball_s ∈ 𝓝 t := hballs_nhd
  have h_diff_ballsupersed : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    filter_upwards [hH'_deriv] with y hy
    intro s' _
    exact hy s' (Set.mem_univ _)
  have h_setInt := hasDerivAt_setIntegral_model (E := E) target htarget_meas
    (F := Fmdl) (F' := Fprim) (b := b) t (s := ball_s) h_s_mem hH_meas_at_t hH_int_at_t
    hH'_meas_at_t h_bound_prop hb_integrable h_diff_ballsupersed
  obtain ⟨_, h_inner⟩ := h_setInt
  -- Convert `∫ y in target, Fmdl t y ∂modelHaar` and `∫ y in target, Fprim t y ∂modelHaar`
  -- back to integrals against the withDensity chart-local measure.
  -- LHS: `fun s => ∫ y in target, Fmdl s y ∂modelHaar = fun s => ∫ x, f s x ∂(withDensity)`.
  have h_lhs_eq : ∀ s : ℝ,
      (∫ y in target, Fmdl s y ∂(modelHaar (E := E)))
        = ∫ x, f s x
            ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
                (fun y : M => ENNReal.ofReal (ρα y))) := by
    intro s
    -- chain: withDensity → ∫ scale • integrand → ∫ ρα · f s d(clm)
    -- then applying integral_chartLocalMeasure to get the target-side integral.
    have hρα_meas : AEMeasurable (fun y : M => ENNReal.ofReal (ρα y))
        (chartLocalMeasure (I := I) (g_fam s) α) :=
      (ENNReal.measurable_ofReal.comp hρα_cont.measurable).aemeasurable
    have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) (g_fam s) α),
        ENNReal.ofReal (ρα y) < ⊤ := Filter.Eventually.of_forall (fun _ => by simp)
    -- LHS unfold using withDensity.
    have h_withD :
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal (ρα y)))
          = ∫ x, (ENNReal.ofReal (ρα x)).toReal • f s x
              ∂(chartLocalMeasure (I := I) (g_fam s) α) :=
      integral_withDensity_eq_integral_toReal_smul₀
        (μ := chartLocalMeasure (I := I) (g_fam s) α)
        (f := fun y : M => ENNReal.ofReal (ρα y)) hρα_meas hρα_lt_top
        (g := f s)
    -- Convert smul to mul.
    have h_smul_eq : (fun x : M =>
        (ENNReal.ofReal (ρα x)).toReal • f s x) = fun x : M => f s x * ρα x := by
      funext x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    -- Apply `integral_chartLocalMeasure` with h_fn := fun x => f s x * ρα x.
    have hfs_cont : Continuous (f s) := by
      have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
        refine hf_cont_joint.comp ?_
        exact continuous_const.prodMk continuous_id
      exact this
    have h_fρ_meas : Measurable (fun x : M => f s x * ρα x) :=
      (hfs_cont.mul hρα_cont).measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam s) α
      (fun x => f s x * ρα x) h_fρ_meas
    -- Stitch together.
    rw [h_withD, h_smul_eq, h_ICLM]
    -- Rearrange integrand on RHS.
    have h_integrand_eq : (fun y : E =>
        chartDensity (I := I) (g_fam s) α (symm y) * (f s (symm y) * ρα (symm y)))
          = fun y : E => Fmdl s y := by
      funext y
      change chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y) *
            (f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y))
        = f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y) *
            chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y)
      ring
    rw [h_integrand_eq]
  -- RHS: `∫ y in target, Fprim t y ∂modelHaar = ∫ x, (∂_t f + 1/2 trace * f) * ρα ∂(clm g_fam t α)`.
  have h_rhs_eq :
      (∫ y in target, Fprim t y ∂(modelHaar (E := E)))
        = ∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              ρα x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) := by
    -- On target ae, Fprim t y = density * (...) * ρα(symm y).
    -- Use `integral_chartLocalMeasure` on g := fun x => (...) * ρα x.
    -- First: set g.
    set gFn : M → ℝ := fun x =>
      (deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρα x
    have hg_cont : Continuous gFn := by
      refine Continuous.mul ?_ hρα_cont
      refine h_deriv_cont.add ?_
      refine Continuous.mul ?_ hft_cont
      exact (continuous_const.mul h_tr_cont)
    have hg_meas : Measurable gFn := hg_cont.measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam t) α gFn hg_meas
    -- Right side: integral against modelHaar over target.
    rw [h_ICLM]
    -- Compare the two integrals via pointwise equality modulo zero-sets.
    refine MeasureTheory.setIntegral_congr_ae htarget_meas ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    -- Fprim t y equals the RHS integrand.
    change (deriv (fun r : ℝ => f r (symm y)) t +
            (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
              f t (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam t) α (symm y)
      = chartDensity (I := I) (g_fam t) α ((extChartAt I α).symm y) *
          gFn ((extChartAt I α).symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) * gFn (symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) *
        ((deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y))
    ring
  -- Combine.
  rw [show (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal (ρα y))))
      = fun s : ℝ => ∫ y in target, Fmdl s y ∂(modelHaar (E := E)) from ?_]
  · rw [h_rhs_eq.symm]
    exact h_inner
  · funext s
    exact (h_lhs_eq s).symm

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

end Volume
end Analysis
end RicciFlower
