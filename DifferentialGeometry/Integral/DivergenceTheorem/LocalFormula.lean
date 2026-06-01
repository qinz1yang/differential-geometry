import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.L2.CompactSupport
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

/-!
# Concrete divergence operator and the Voss–Weyl local formula

For a smooth Riemannian metric `g` on the tangent bundle of a smooth manifold `M`
and a smooth tangent section `X`, this file defines the divergence
`divergence_g g X : M → ℝ` directly via a chart-local formula, independently of
any abstract connection structure.

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

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- The `i`-th chart-basis component of a smooth tangent section `X` in the
trivialization at `α`. On the trivialization base set, this satisfies
`X x = ∑ i, chartCoeff α X i x • chartBasisVecFiber α i x`; off the base set
the value is given by the trivialization's junk extension. -/
def chartCoeff (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x => (chartModelBasis E).repr
    ((trivializationAt E (TangentSpace I) α) ⟨x, X x⟩).2 i

@[simp] lemma chartCoeff_def (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartCoeff (I := I) α X i x =
      (chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) α) ⟨x, X x⟩).2 i := rfl

/-- On the chart base set, the smooth section `X` is reconstructed from its
chart-basis components using the chart-basis frame. -/
lemma chartCoeff_recompose (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    X x = ∑ i, chartCoeff (I := I) α X i x •
      chartBasisVecFiber (I := I) α i x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  set L : TangentSpace I x ≃L[ℝ] E := T.continuousLinearEquivAt ℝ x hx
  have hL : L (X x) = (T ⟨x, X x⟩).2 := rfl
  have hLsymm : ∀ v : E, L.symm v = T.symm x v := fun _ => rfl
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  have hdecomp : (T ⟨x, X x⟩).2 =
      ∑ i, b.repr ((T ⟨x, X x⟩).2) i • b i := by
    have := (Module.Basis.sum_repr b ((T ⟨x, X x⟩).2))
    exact this.symm
  have hX : X x = L.symm ((T ⟨x, X x⟩).2) := by
    rw [← hL, L.symm_apply_apply]
  rw [hX, hdecomp, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  simp only [chartCoeff_def, chartBasisVecFiber]
  rfl

/-- The chart-basis component is smooth on the chart base set. The proof uses
the smoothness of the trivialization (a `ContMDiffSection` is mapped through
the trivialization to a smooth function valued in `E`), then composes with the
continuous linear evaluation `b.repr · i`. -/
lemma chartCoeff_contMDiffOn (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) α X i)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% fun x : M => X x) := X.contMDiff
  have hiff :=
    T.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞) (s := fun x : M => X x)
  have hsection : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun x : M => (T ⟨x, X x⟩).2) T.baseSet := hiff.mp hX.contMDiffOn
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  set Lcoord : E →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  have hLcoord_contDiff : ContDiff ℝ ∞ (Lcoord : E → ℝ) := Lcoord.contDiff
  have hcomp : ContMDiffOn I 𝓘(ℝ) ∞
      ((Lcoord : E → ℝ) ∘ (fun x : M => (T ⟨x, X x⟩).2)) T.baseSet :=
    hLcoord_contDiff.contMDiff.comp_contMDiffOn hsection
  have heq : (Lcoord : E → ℝ) ∘ (fun x : M => (T ⟨x, X x⟩).2)
      = chartCoeff (I := I) α X i := by
    funext x
    change Lcoord ((T ⟨x, X x⟩).2) = (chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) α) ⟨x, X x⟩).2 i
    change (b.coord i) ((T ⟨x, X x⟩).2) = _
    rw [Module.Basis.coord_apply]
  rw [← heq]
  exact hcomp

/-- The chart-basis component pulled back through the inverse extended chart at
`α`, viewed as a function on the chart target `(extChartAt I α).target ⊆ E`. -/
def chartCoeffOnE (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartCoeff (I := I) α X i ((extChartAt I α).symm y)

/-- The chart density pulled back through the inverse extended chart at `α`,
viewed as a function on the chart target. -/
def chartDensityOnE (g : SmoothRiemannianMetric I M) (α : M) : E → ℝ :=
  fun y => chartDensity (I := I) g α ((extChartAt I α).symm y)

/-- The partial derivative of a function `u : E → ℝ` at `y : E` in the
direction of the `i`-th model-basis vector. -/
def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((chartModelBasis E) i)

/-- The chart-local Voss–Weyl divergence in the chart at `α`, as a function
on `M`. The defining identity:
`localDivergence g α X x · sqrt(det G_α(x)) = ∑ i, partialDeriv i (X^i · sqrt det G_α) (φ_α x)`. -/
def localDivergence (g : SmoothRiemannianMetric I M)
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    M → ℝ := fun x =>
  (∑ i : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
        (extChartAt I α x))
    / chartDensity (I := I) g α x

@[simp] lemma localDivergence_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    localDivergence (I := I) g α X x =
      (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun y => chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

/-- The chart-inverse map `(extChartAt I α).symm` sends every point of the chart
target into the trivialization base set at `α`. -/
private lemma extChartAt_symm_mapsTo_baseSet (α : M) :
    Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro y hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  exact hsource

/-- The chart-pulled-back component `chartCoeffOnE α X i` is `C^∞` on the chart
target. Proof: compose `chartCoeff_contMDiffOn` with the smoothness of
`(extChartAt I α).symm` on the target, then pass from manifold-smoothness to
ordinary smoothness on the model space `E`. -/
lemma chartCoeffOnE_contDiffOn (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α X i) (extChartAt I α).target := by
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) α X i)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartCoeff_contMDiffOn (I := I) α X i
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet :=
    fun y hy => extChartAt_symm_mapsTo_baseSet (I := I) α hy
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((chartCoeff (I := I) α X i) ∘ (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-- The chart-pulled-back density `chartDensityOnE g α` is `C^∞` on the chart
target. Same composition pattern as `chartCoeffOnE_contDiffOn`. -/
lemma chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α) (extChartAt I α).target := by
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_contMDiffOn (I := I) g α
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet :=
    fun y hy => extChartAt_symm_mapsTo_baseSet (I := I) α hy
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((chartDensity (I := I) g α) ∘ (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-- The integrand `y ↦ chartCoeffOnE α X i y * chartDensityOnE g α y` of the
Voss–Weyl chart formula is `C^∞` on the chart target. Direct from
`chartCoeffOnE_contDiffOn` and `chartDensityOnE_contDiffOn` via `ContDiffOn.mul`. -/
lemma chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
  (chartCoeffOnE_contDiffOn (I := I) α X i).mul
    (chartDensityOnE_contDiffOn (I := I) g α)

/-- The partial derivative `y ↦ partialDeriv i u y` is `C^∞` on the interior of
any set on which `u` itself is `C^∞`. -/
private lemma partialDeriv_contDiffOn_interior
    (i : Fin (Module.finrank ℝ E)) {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) i u) (interior s) := by
  have hu_int : ContDiffOn ℝ ∞ u (interior s) := hu.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior s) :=
    hu_int.fderiv_of_isOpen isOpen_interior
      (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
      (interior s) := contDiffOn_const
  exact hfderiv.clm_apply hconst

/-- For a smooth tangent section `X` and base point `α`, the partial derivative
`y ↦ partialDeriv i (chartCoeffOnE α X i · * chartDensityOnE g α ·) y` is
`C^∞` on the interior of the chart target. -/
lemma partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior i
    (chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i)

/-- The smoothness domain we use for the chart-local Voss–Weyl divergence: the
points in the chart base set whose image under the chart map lies in the
interior of the chart target. -/
private def localDivergenceDomain (α : M) : Set M :=
  (extChartAt I α).source ∩
    (extChartAt I α) ⁻¹' interior (extChartAt I α).target

private lemma localDivergenceDomain_subset_baseSet (α : M) :
    localDivergenceDomain (I := I) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
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
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
    partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (localDivergenceDomain (I := I) α) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
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

/-- The chart-local Voss–Weyl divergence is `C^∞` on the natural smoothness
domain — points of the chart source whose chart image lies in the interior of
the chart target. -/
theorem localDivergence_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  have hnum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (localDivergenceDomain (I := I) α) :=
    contMDiffOn_finset_sum
      (fun i _ => localDivergence_summand_contMDiffOn (I := I) g α X i)
  have hden :
      ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
        (localDivergenceDomain (I := I) α) :=
    chartDensity_contMDiffOn_localDivergenceDomain (I := I) g α
  exact hnum.div₀ hden
    (chartDensity_ne_zero_on_localDivergenceDomain (I := I) g α)

/-- The global divergence of a smooth tangent section `X` with respect to a
smooth Riemannian metric `g`. By definition, it evaluates at `x` to the
chart-local Voss–Weyl formula in the chart at `x`. -/
def divergence_g (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergence (I := I) g x X x

@[simp] lemma divergence_g_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g X x = localDivergence (I := I) g x X x := rfl

end DivergenceTheorem
end Integral
end DifferentialGeometry
