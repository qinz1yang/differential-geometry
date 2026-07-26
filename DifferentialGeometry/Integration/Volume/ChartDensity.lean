import DifferentialGeometry.Geometry.Metric.MetricBallMonotone
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Metric.ChartGram

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Chart-local volume density from a Riemannian metric

Given a smooth `ContMDiffRiemannianMetric` `g` on the tangent bundle of a manifold `M`
and a base point `x₀ : M`, we construct a chart-local positive smooth density on the
domain of the base chart at `x₀`, and the associated chart-local Borel measure on `M`.

## Overview

Inside the open set `triv.baseSet = (chartAt H x₀).source`, we build a pointwise basis of
the tangent bundle by transporting a fixed algebraic basis of the model space `E` through
the tangent-bundle trivialization centred at `x₀`. The Gram matrix of this basis under
`g` is symmetric positive-definite, so its determinant is strictly positive and its
square root gives a positive smooth density on the chart domain.

The chart-local measure is obtained by weighting a chosen reference measure on the model
space `E` by the pullback of this density through the extended chart, and then pushing
forward to `M`.

## Main definitions

* `chartBasisVec g x₀ i` : the tangent-bundle section over `triv.baseSet` whose value
  at `x` is the image of the `i`-th model-space basis vector under the inverse of the
  tangent trivialization centred at `x₀`.
* `chartGramMatrix g x₀ x` : the Gram matrix at `x` of the family `chartBasisVec g x₀ •`
  under the inner product `g.inner x`.
* `chartDensity g x₀ x` : the positive density `√(det (chartGramMatrix g x₀ x))`.
* `chartLocalMeasure g x₀` : the chart-local measure on `M` obtained by pushing
  forward the weighted canonical additive Haar measure on the model space `E`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Canonical measurable-space and Borel-space instances on `E` and `M`

These are file-local instances that equip any finite-dimensional real normed space `E`
with its Borel σ-algebra and any topological manifold `M` with the Borel σ-algebra
induced from its topology. They are declared `local` so they do not leak into calling
files as global instances; callers that need to interact with the measures defined below
should install matching instances in their own scope. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩





private lemma chartGramMatrix_pair_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  chartGramMatrix_entry_contMDiffOn (I := I) g x₀ ij.1 ij.2



end DifferentialGeometry.Integral.Measure
