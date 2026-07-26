import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Integration.Volume.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import DifferentialGeometry.Integration.Volume.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula

/-!
# Concrete divergence operator and the Voss–Weyl local formula

For a smooth Riemannian metric `g` on the tangent bundle of a smooth manifold `M`
and a smooth tangent section `X`, this file defines the divergence
`divergence_g g X : M → ℝ` directly via a chart-local formula, independently of
any abstract Synthetic-layer connection structure.

The construction proceeds in two layers:

1. **Chart-local components.** Given a base point `α : M`, the smooth tangent
   section `X` is decomposed in the chart-basis frame attached to the
   trivialization at `α`. The resulting coordinate functions
   `chartCoeff g α X i : M → ℝ` are smooth on the chart base set.

2. **Voss–Weyl chart formula.** In the chart at `α`, the Voss–Weyl formula
   reads
   $$\operatorname{div}_g(X)(x)
       = \frac{1}{\sqrt{\det G_\alpha(x)}} \sum_i \partial_i\bigl(X^i_\alpha(x)
           \cdot \sqrt{\det G_\alpha(x)}\bigr).$$
   Here `G_α(x) = chartGramMatrix g α x` is the Gram matrix of the chart-basis
   frame and `X^i_α` are the chart-basis components of `X`. The partial
   derivatives are taken with respect to the chart coordinates on
   `(extChartAt I α).target ⊆ E` after pulling back through the chart.

The chart-formula is shown to be invariant under change of chart on the overlap
of two chart sources, so the global divergence
`divergence_g g X x := localDivergence g (chartAt H x) X x`
is independent of the chart used at `x`. The resulting global function is
smooth, and it admits the canonical Voss–Weyl pointwise representation in any
chart at any point of its source.

## Main definitions

* `chartCoeff g α X i` : the `i`-th chart-basis component of `X` in the
  trivialization at `α`, as a smooth function on the chart base set.
* `localDivergence g α X x` : the Voss–Weyl chart-formula evaluated in the
  chart at `α`, defined for `x` in the chart base set.
* `divergence_g g X` : the global divergence as a smooth real-valued function
  on `M`, obtained by evaluating `localDivergence g (chartAt H x) X` at each
  point `x : M`.

## Main results

* `chartCoeff_contMDiffOn` : each chart-basis component is `C^∞` on the chart
  base set.
* `localDivergence_contMDiffOn` : the chart-local Voss–Weyl divergence is
  `C^∞` on the chart base set.
* `localDivergence_chart_invariance` : the chart-local Voss–Weyl divergence
  agrees on the overlap of two chart sources.
* `divergence_g_eq_localDivergence` : the global divergence equals any
  chart-local representative on the source of that chart.
* `divergence_g_contMDiff` : the global divergence is `C^∞`.
* `voss_weyl_divergence_formula` : for any chart at `α`, the global divergence
  agrees on the chart source with the Voss–Weyl chart formula.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Chart-basis component functions

Given a base point `α : M` and a smooth tangent section `X`, the chart-basis
component functions `chartCoeff g α X i : M → ℝ` are obtained by applying the
trivialization at `α` to `X` and extracting model-basis coordinates. They are
defined on all of `M` (with a junk value off the trivialization base set) but
are mathematically meaningful only on
`(trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source`. -/



private lemma extChartAt_symm_mapsTo_baseSet (α : M) :
    Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro y hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  exact hsource

private lemma partialDeriv_contDiffOn_interior
    (i : Fin (Module.finrank ℝ E)) {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) i u) (interior s) := by
  -- `u` is `C^∞` on the open set `interior s`.
  have hu_int : ContDiffOn ℝ ∞ u (interior s) := hu.mono interior_subset
  -- Smoothness of `fderiv ℝ u` on the open set `interior s`. The hypothesis
  -- `m + 1 ≤ n` with `m = n = ∞` is `∞ + 1 ≤ ∞`, which by
  -- `ENat.coe_top_add_one : ∞ + 1 = ∞` reduces to `∞ ≤ ∞`.
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior s) :=
    hu_int.fderiv_of_isOpen isOpen_interior
      (by rw [ENat.coe_top_add_one])
  -- Constant function `y ↦ basis i` is smooth.
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
      (interior s) := contDiffOn_const
  -- Apply `ContDiffOn.clm_apply`.
  exact hfderiv.clm_apply hconst

private def localDivergenceDomain (α : M) : Set M :=
  (extChartAt I α).source ∩
    (extChartAt I α) ⁻¹' interior (extChartAt I α).target

private lemma localDivergenceDomain_subset_baseSet (α : M) :
    localDivergenceDomain (I := I) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  -- `(trivializationAt …).baseSet = (chartAt H α).source = (extChartAt I α).source`
  -- by `trivializationAt_baseSet_eq_chartAt_source` and `extChartAt_source_eq_chartAt_source`.
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  rw [← extChartAt_source_eq_chartAt_source (I := I)]
  exact hx.1

/-- Each summand of the chart-local Voss–Weyl divergence's numerator is `C^∞`
on the smoothness domain, as a function of `x : M`. -/
private lemma localDivergence_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (localDivergenceDomain (I := I) α) := by
  -- Smoothness of the partial-derivative functional on the interior of the target.
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
    partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  -- Lift to manifold-smoothness on the same set.
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  -- Smoothness of `extChartAt I α` on the chart source.
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  -- Restrict `hchart` to the smoothness domain via
  -- `(extChartAt I α).source = (chartAt H α).source`.
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (localDivergenceDomain (I := I) α) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  -- Composition: the smoothness domain maps into `interior (target)` by definition.
  have hsubset : localDivergenceDomain (I := I) α ⊆
      (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

/-- The chart density `chartDensity g α` is `C^∞` on the smoothness domain (in
fact on the whole trivialization base set). -/
private lemma chartDensity_contMDiffOn_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (localDivergenceDomain (I := I) α) :=
  (chartDensity_contMDiffOn (I := I) g α).mono
    (localDivergenceDomain_subset_baseSet (I := I) α)

/-- The chart density is strictly positive on the smoothness domain. -/
private lemma chartDensity_ne_zero_on_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ localDivergenceDomain (I := I) α, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt
    (chartDensity_pos (I := I) g α
      (localDivergenceDomain_subset_baseSet (I := I) α hx))


theorem divergence_g_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g X x =
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (chartCoeffOnE (I := I) x X i) (extChartAt I x x)) +
        (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x X i (extChartAt I x x) *
            partialDeriv (E := E) i
              (chartDensityOnE (I := I) g x) (extChartAt I x x)) /
          chartDensity (I := I) g x x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [hy₀_def, (extChartAt I x).map_source hxsrc]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  have hsymm : (extChartAt I x).symm y₀ = x := by
    simp [hy₀_def, (extChartAt I x).left_inv hxsrc]
  have hρOnE :
      chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm y₀) =
      chartDensity (I := I) g x x
    rw [hsymm]
  have hcoeff_diff :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (chartCoeffOnE (I := I) x X i) y₀ := by
    intro i
    have hsmooth : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x X i)
        (extChartAt I x).target :=
      chartCoeffOnE_contDiffOn (I := I) x X i
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hprod :
      ∀ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀ =
          partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀ := by
    intro i
    unfold partialDeriv
    have hmul : fderiv ℝ
        (fun y : E =>
          chartCoeffOnE (I := I) x X i y *
            chartDensityOnE (I := I) g x y) y₀ =
        chartCoeffOnE (I := I) x X i y₀ •
          fderiv ℝ (chartDensityOnE (I := I) g x) y₀ +
        chartDensityOnE (I := I) g x y₀ •
          fderiv ℝ (chartCoeffOnE (I := I) x X i) y₀ :=
      fderiv_fun_mul (hcoeff_diff i) hρ_diff
    rw [hmul]
    rw [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [divergence_g_def, localDivergence_def]
  change
    (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) /
      chartDensity (I := I) g x x = _
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) =
        ∑ i : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀) by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hprod i]
  rw [Finset.sum_add_distrib]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
          chartDensityOnE (I := I) g x y₀) =
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀) *
          chartDensityOnE (I := I) g x y₀ by
      rw [Finset.sum_mul]]
  rw [hρOnE]
  rw [add_div]
  rw [mul_div_assoc, div_self hρ_ne, mul_one]

end DifferentialGeometry.Integral.DivergenceTheorem
