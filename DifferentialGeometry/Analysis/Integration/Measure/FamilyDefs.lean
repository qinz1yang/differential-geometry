import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Time-parameterised Riemannian volume measure: families, regularity interfaces,
# and the chart-density Jacobi corollary

This file collects the definitional layer underlying the first variation of
volume: the family of Riemannian volume measures attached to a time-varying
metric, the minimal regularity interfaces for a metric family and a scalar
integrand, the chart-local Gram-matrix and density families, the pointwise
chart-density Jacobi formula, and the intrinsic metric trace
`tr_g(∂_t g)` of the time-derivative.

## Main definitions

* `riemannianMeasureFamily g_fam` : the family `t ↦ riemannianVolumeMeasure (g_fam t)`.
* `MetricFamilyRegularAt g_fam t₀` : the pointwise regularity interface used by
  the volume variation machinery (pointwise `HasDerivAt` + joint continuity on
  chart base sets — no joint smoothness).
* `FunctionRegularAt f t₀` : the analogous interface for a scalar integrand.
* `chartGramMatrixFamily` / `chartDensityFamily` : the chart-local Gram matrix
  and density of the family at a fixed spatial point, as functions of time.
* `traceTimeDerivMetric g_fam t x` : the intrinsic metric trace `tr_g(∂_t g)(x)`,
  computed in the canonical chart at `x`.

## Main results

* `hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul` : the pointwise Jacobi
  formula for the chart density, the half-trace-of-inverse form.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Given a smoothly-time-parameterised Riemannian metric family, the associated
family of Riemannian volume measures on `M`. -/
def riemannianMeasureFamily
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) : ℝ → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)

/-- Unfolding lemma for the time-parameterised Riemannian volume measure. -/
lemma riemannianMeasureFamily_def
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t) := rfl

/-- Minimum regularity interface for a time-varying Riemannian metric family at a
base time. Encapsulates exactly the pointwise time-differentiability and joint
`(t, x)`-continuity required by the volume-variation formula.

Note: the first field asserts differentiability at every time `t`, not just `t₀`.
The parametric-integral theorem used downstream requires the time-derivative to
exist in a neighbourhood of `t₀`, and supplying it at every time is the natural
minimal strengthening (and is automatic for any family arising from a smooth
Ricci-flow solution or any other jointly-smooth source). -/
structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where

  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t

  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

/-- The regularity interface is time-agnostic: its fields depend on the base
time only as an existential quantifier parameter. So `MetricFamilyRegularAt g_fam t`
yields `MetricFamilyRegularAt g_fam s` for any other time `s` trivially. -/
lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s :=
  { hasDerivAt_chartGramMatrix := hreg.hasDerivAt_chartGramMatrix
    continuousOn_chartGramMatrix := hreg.continuousOn_chartGramMatrix
    continuousOn_deriv_chartGramMatrix := hreg.continuousOn_deriv_chartGramMatrix }

/-- Minimum regularity interface for a time-varying real-valued function on `M`.

Note: `hasDerivAt_time` asserts differentiability at every time, not just `t₀`.
The parametric-integral theorem used downstream requires differentiability in a
neighbourhood of `t₀`; supplying it at every time is the natural minimal
strengthening (and is automatic for any jointly-smooth source). -/
structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where

  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t

  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)

  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

/-- The Gram matrix of the chart-local basis, as a family in time. At each time
`t`, `Gfam t x = chartGramMatrix (g_fam t) x₀ x`. -/
def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => chartGramMatrix (I := I) (g_fam t) x₀ x

@[simp] lemma chartGramMatrixFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartGramMatrixFamily (I := I) g_fam x₀ x t =
      chartGramMatrix (I := I) (g_fam t) x₀ x := rfl

/-- The chart density of the time-parameterised family at a fixed spatial point. -/
def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

@[simp] lemma chartDensityFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      chartDensity (I := I) (g_fam t) x₀ x := rfl

lemma chartDensityFamily_eq_sqrt_det
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := rfl

/-- Pointwise Jacobi formula applied to the chart density: given a family
of Gram matrices with each entry differentiable in time, the derivative of the
density is given by the standard half-trace-of-inverse formula multiplied by
the density itself, at any point in the chart base set. -/
theorem hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M) (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam x₀ x s i j)
        (Gprime i j) t) :
    HasDerivAt
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
      ((1 / 2) *
        trace ((chartGramMatrixFamily (I := I) g_fam x₀ x t)⁻¹ * Gprime) *
        Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det) t := by
  have hpos : 0 < (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := by
    simpa [chartGramMatrixFamily_apply] using
      chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx
  have hderiv := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := chartGramMatrixFamily (I := I) g_fam x₀ x)
    (G' := Gprime) (t := t) hEntries hpos
  have hfun :
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
        = (fun s => Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x s).det) := by
    funext s
    exact chartDensityFamily_eq_sqrt_det (I := I) g_fam x₀ x s
  rw [hfun]
  exact hderiv

end ChartDensityFamily

variable (I) in
/-- The metric trace `tr_g(∂_t g)(x)` at time `t`, computed in the canonical
chart at `x`. Concretely, with `G(s) := chartGramMatrix (g_fam s) x x`, this is
`trace(G(t)⁻¹ · G'(t))`, where `G'(t)` is the matrix of pointwise time
derivatives. Since `x ∈ (chartAt H x).source` always, the base set contains
`x` and the Jacobi machinery applies. -/
def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t))

/-- Unfolding lemma for `traceTimeDerivMetric`. -/
lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

end Measure
end Integral
end DifferentialGeometry
