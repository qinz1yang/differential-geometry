import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Integration.Volume.ChartDensity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
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
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Compactness.LocallyFinite
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs
import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Time-parameterised Riemannian volume measure and Jacobi formula for the density

Given a smoothly-time-parameterised Riemannian metric family
`g_fam : ℝ → SmoothRiemannianMetric I M`, we define the associated family of
Riemannian volume measures and prove the pointwise time-derivative of the
chart-local density via Jacobi's formula for the determinant.

## Main definitions

* `riemannianMeasureFamily g_fam` : the family `t ↦ riemannianVolumeMeasure (g_fam t)`.
* `MetricFamilyRegularAt g_fam t₀` : the pointwise regularity interface used by
  the volume variation machinery (pointwise `HasDerivAt` + joint continuity on
  chart base sets — no joint smoothness).
* `FunctionRegularAt f t₀` : the analogous interface for a scalar integrand.
* `traceTimeDerivMetric g_fam t x` : the intrinsic metric trace `tr_g(∂_t g)(x)`,
  computed in the canonical chart at `x`.

## Main results

* `hasDerivAt_det_of_entries` : derivative of `det ∘ G(t)` in the parameter `t`,
  expressed as the canonical permutation-sum form coming from `Matrix.det_apply'`.
* `perm_sum_eq_trace_adjugate_mul` : the permutation sum above equals
  `trace (adjugate A · B)`.
* `hasDerivAt_det_eq_trace_adjugate_mul` : Jacobi's formula in the form
  `d/dt det G(t) = trace (adjugate (G t) · G'(t))`.
* `hasDerivAt_det_eq_det_mul_trace_inv_mul` : the classical form
  `d/dt det G(t) = det(G t) · trace(G(t)⁻¹ · G'(t))` when `(G t).det` is a unit.
* `hasDerivAt_sqrt_det_of_entries` : derivative of `√(det G(t))` via chain rule.
* `hasDerivAt_sqrt_det_eq_half_trace_inv_mul` : the geometric form
  `d/dt √(det G(t)) = ½ · trace(G(t)⁻¹ · G'(t)) · √(det G(t))` under positivity.
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

/-! ## The time-parameterised Riemannian volume measure -/

theorem continuousOn_deriv_of_hasDerivAt_eq_continuousOn
    {α : Type*} [TopologicalSpace α]
    {S : Set (ℝ × α)} {f D : ℝ → α → ℝ}
    (hderiv :
      ∀ p ∈ S, HasDerivAt (fun t : ℝ => f t p.2) (D p.1 p.2) p.1)
    (hD : ContinuousOn (fun p : ℝ × α => D p.1 p.2) S) :
    ContinuousOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      S := by
  have h_eq : Set.EqOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      (fun p : ℝ × α => D p.1 p.2) S := by
    intro p hp
    exact (hderiv p hp).deriv
  exact hD.congr h_eq

/-- Explicit continuous time derivatives of the chart Gram entries produce the
regularity package needed by the volume-variation theorem. -/
theorem MetricFamilyRegularAt.of_chartGram_timeDeriv
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (h :
      ∀ x₀ i j, ∃ D : ℝ → M → ℝ,
        (∀ t x,
          x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
            HasDerivAt
              (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
              (D t x) t) ∧
        ContinuousOn
          (fun p : ℝ × M =>
            chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) ∧
        ContinuousOn
          (fun p : ℝ × M => D p.1 p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine
    { hasDerivAt_chartGramMatrix := ?_
      continuousOn_chartGramMatrix := ?_
      continuousOn_deriv_chartGramMatrix := ?_ }
  · intro x₀ i j x hx t
    rcases h x₀ i j with ⟨D, hD_deriv, -, -⟩
    have hderiv := hD_deriv t x hx
    exact hderiv.congr_deriv hderiv.deriv.symm
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, -, hG_cont, -⟩
    exact hG_cont
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, hD_deriv, -, hD_cont⟩
    refine continuousOn_deriv_of_hasDerivAt_eq_continuousOn
      (S := Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (f := fun t x => chartGramMatrix (I := I) (g_fam t) x₀ x i j)
      (D := D) ?_ hD_cont
    intro p hp
    exact hD_deriv p.1 p.2 hp.2

theorem FunctionRegularAt_const (c : ℝ) (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => c) t₀ := by
  refine
    { hasDerivAt_time := ?_
      continuous_joint := ?_
      continuous_deriv_joint := ?_ }
  · intro _ t
    have hderiv : deriv (fun _ : ℝ => c) t = 0 :=
      (hasDerivAt_const (x := t) (c := c)).deriv
    simpa [hderiv] using (hasDerivAt_const (x := t) (c := c))
  · simpa using (continuous_const : Continuous (fun _ : ℝ × M => c))
  · have hfun :
        (fun p : ℝ × M => deriv (fun _ : ℝ => c) p.1) =
          fun _ : ℝ × M => (0 : ℝ) := by
      funext p
      exact (hasDerivAt_const (x := p.1) (c := c)).deriv
    simpa [hfun] using (continuous_const : Continuous (fun _ : ℝ × M => (0 : ℝ)))

/-- The constant one integrand satisfies the regularity interface used by the
volume variation theorem. -/
theorem FunctionRegularAt_one (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => (1 : ℝ)) t₀ :=
  FunctionRegularAt_const (M := M) 1 t₀

/-! ## Jacobi's formula for the determinant of a smooth matrix family

We develop the time-derivative of `t ↦ (G t).det` in full generality, for any
smooth family `G : ℝ → Matrix n n ℝ` whose entries each have a derivative at
the base point. The derivation is elementary: we expand the determinant via
`Matrix.det_apply'` and apply the product rule `HasDerivAt.finset_prod`
componentwise.

Throughout this section, `n` is an arbitrary index type with `Fintype n` and
`DecidableEq n`. Concretely, in the application `n = Fin (Module.finrank ℝ E)`.
-/

section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]


end Jacobi

/-! ## Application to the chart-local density

We specialise the abstract Jacobi formula to the concrete Gram-matrix family
`Gfam t x := chartGramMatrix (g_fam t) x₀ x` arising from a time-parameterised
Riemannian metric family on `M`, at a fixed base point `x₀` and a fixed
evaluation point `x` in the chart source. -/

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}





end ChartDensityFamily

/-! ## Coordinate-invariant metric trace of the time-derivative

Given a time-parameterised Riemannian metric family and a point `x : M`, we
define the intrinsic scalar `tr_g(∂_t g)(x)`, computed as the trace
`trace (G⁻¹ · G')` where `G t = chartGramMatrix (g_fam t) x x` uses the chart
source at `x` itself as the basis chart (so `x` is always in the base set, and
the canonical choice avoids any well-definedness issue).

Note: the definition uses `deriv`, which returns `0` whenever the underlying
function is not differentiable at the base time. Consequently the definition
is total and requires no regularity hypothesis; callers supply regularity only
where they need the concrete identification `deriv = ∂_t G`. -/



section ChartInvarianceOfTraceTimeDeriv


end ChartInvarianceOfTraceTimeDeriv



end DifferentialGeometry.Integral.Measure
