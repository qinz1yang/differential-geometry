import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradChartIdentity

/-!
# The chart-component formula for the covariant *second* gradient of a `(0,2)`-tensor

For a closed Riemannian manifold `(M, g)` modelled on a real inner-product space
`E` and a smooth compactly-supported `(0, 2)`-tensor section `h`, the iterated
covariant gradient `iteratedCovGrad g 0 2 2 h = ∇²h` is a smooth
compactly-supported `(0, 4)`-tensor section.  This file relates its raw
chart-frame components to the *chart Hessian* of the chart components of `h` —
the bridge underpinning the mean-value transfer (relating the chart Hessian
`∂²h` to the covariant second gradient `∇₀²h`).

## The bridge

By the recursion `iteratedCovGrad g 0 2 2 h = covGrad g 0 3 (covGrad g 0 2 h)`
(`iteratedCovGrad_succ`/`iteratedCovGrad_zero`) and the single-`covGrad` raw
chart-component formula `tensorChartComponentRaw_covGrad` (covariant derivative =
chart partial − Christoffel correction), the raw chart component of `∇²h` at a
target multi-index `Jdx : Fin 3 → Fin n` (no contravariant slots since `r = 0`),
read at the chart-source preimage of a chart-target point `y`, decomposes as
follows.

* `chartCovariantSecondGrad_eq` (outer step): the `(Jdx 0)`-th chart-Euclidean
  partial of the Euclidean push-forward of the raw chart component of the *first*
  covariant gradient `covGrad g 0 2 h` (at the tail multi-index `vecTail Jdx`),
  plus the zeroth-order Christoffel correction term `covDerivLowerOrderTerm` for
  that first gradient.

* `chartCovariantSecondGrad_inner` (inner step): the same single-`covGrad`
  formula applied to `covGrad g 0 2 h`, expressing its chart component as a
  chart-Euclidean partial of the raw component of `h` plus the Christoffel
  correction for `h`.

Substituting the inner step pointwise inside the lower-order term, and (using
that `chartTargetEuclid α` is open and the inner identity holds on it) under the
outer partial derivative via `fderiv` congruence, exhibits the leading term as
the genuine chart Hessian `∂_{Jdx 0} ∂_{Jdx 1}` of the chart component of `h`
itself.  This is the standard "covariant Hessian = chart Hessian − Christoffel
corrections" decomposition for a `(0,2)`-tensor; the corrections are exactly the
`Γ·∂h + (∂Γ + ΓΓ)·h` structure (numerically: 5 `Γ·∂h`, 2 `(∂Γ)·h`, 6 `ΓΓ·h`
terms when fully expanded by slot), grouped here as the two
`covDerivLowerOrderTerm` applications.

## Layering note

The reasoning here is chart-Sobolev component analysis: both ingredients
(`iteratedCovGrad`, whose recursion lives with the `C^m` tensor Sobolev
embedding, and `tensorChartComponentRaw_covGrad`) are analytic.  The file
therefore lives in the analysis pillar, next to the single-`covGrad` chart
identity it iterates.  It cannot live under `Geometry/Connection/TensorNabla/`:
the covariant-gradient chart machinery in `Analysis/` transitively imports back
into `Geometry/Connection/TensorNabla/`, so importing it from there would form a
Lean import cycle.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **The raw chart-component formula for the covariant second gradient of a
`(0,2)`-tensor (outer step).**

For a smooth compactly-supported `(0, 2)`-tensor section `h`, a chart center `α`,
a target covariant multi-index `Jdx : Fin 3 → Fin n`, and a chart-target point
`y`, the raw chart-frame scalar component of the covariant second gradient
`iteratedCovGrad g 0 2 2 h` (a `(0, 4)`-tensor; `r = 0`, so the contravariant
multi-index is the unique `Fin 0` map `Idx`), read at the chart-source preimage
`b := (extChartAt I α).symm (toEuclidean.symm y)` of `y`, equals the `(Jdx 0)`-th
chart-Euclidean partial derivative of the Euclidean push-forward of the raw chart
component of the first covariant gradient `covGrad g 0 2 h` at the tail
multi-index `Matrix.vecTail Jdx`, plus the zeroth-order Christoffel correction
term `covDerivLowerOrderTerm` for `covGrad g 0 2 h`.

This is one application of the single-`covGrad` formula
`tensorChartComponentRaw_covGrad` to the outer covariant gradient of
`iteratedCovGrad g 0 2 2 h = covGrad g 0 3 (covGrad g 0 2 h)`. -/
theorem chartCovariantSecondGrad_eq
    (g : SmoothRiemannianMetric I M) (h : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g 0 (2 + 2)
        (iteratedCovGrad (I := I) g 0 2 2 h) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 h) α Idx (Matrix.vecTail Jdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 h) α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  have hrec : iteratedCovGrad (I := I) g 0 2 2 h =
      covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 h) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hrec]
  exact tensorChartComponentRaw_covGrad (I := I) (M := M) g 0 3
    (covGrad (I := I) (M := M) g 0 2 h) α Idx Jdx hy

/-- **The raw chart-component formula for the first covariant gradient of a
`(0,2)`-tensor (inner step).**

This is `tensorChartComponentRaw_covGrad` specialised to `r = 0`, `s = 2`, applied
to `h` itself: the raw chart component of `covGrad g 0 2 h` (a `(0, 3)`-tensor) at
a multi-index `Kdx : Fin 3 → Fin n`, read at the chart-source preimage of `y`,
equals the `(Kdx 0)`-th chart-Euclidean partial of the Euclidean push-forward of
the raw chart component of `h` at `Matrix.vecTail Kdx`, plus the Christoffel
correction `covDerivLowerOrderTerm` for `h`.  It supplies the inner expansion
substituted into `chartCovariantSecondGrad_eq` to expose the chart Hessian of
`h`. -/
theorem chartCovariantSecondGrad_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Kdx : Fin 3 → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 h) α Idx Kdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Kdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2
            h α Idx (Matrix.vecTail Kdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g 0 2 h α (Kdx 0) Idx
            (Matrix.vecTail Kdx) y :=
  tensorChartComponentRaw_covGrad (I := I) (M := M) g 0 2 h α Idx Kdx hy

/-- **The covariant Hessian = chart Hessian − Christoffel corrections
decomposition for a `(0,2)`-tensor.**

Composing the outer step `chartCovariantSecondGrad_eq` with the inner step
`chartCovariantSecondGrad_inner` (substituted *under* the outer chart partial via
the eventually-equal congruence `euclidPartial_congr_of_eqOn_open`, valid because
`chartTargetEuclid α` is open and the inner identity holds throughout it), the raw
chart component of the covariant second gradient `iteratedCovGrad g 0 2 2 h` at a
target multi-index `Jdx : Fin 4 → Fin n` decomposes as:

* the **chart Hessian** of `h`'s own raw chart component — the iterated
  chart-Euclidean partial `euclidPartial (Jdx 0) (euclidPartial ((vecTail Jdx) 0)
  (chartPushedRaw h-component))`, the term that would be the whole answer were the
  connection flat — written here as the `(Jdx 0)`-partial of the
  *Christoffel-corrected first-gradient component* (the inner step is kept under
  the outer partial, so the term reads `∂_{Jdx 0}[∂_{(vecTail Jdx) 0}(chartComp h)
  + Γ·h]`, which is `∂²(chartComp h) + ∂(Γ·h)`, i.e. the chart Hessian plus the
  derivative of the first-order Christoffel correction);

* **minus / plus the zeroth-order Christoffel correction** of the *outer*
  covariant gradient, `covDerivLowerOrderTerm g 0 3 (covGrad g 0 2 h) …`, the
  `Γ·∇h` term.

Together these are precisely the `Γ·∂h + (∂Γ + ΓΓ)·h` correction structure for a
`(0,2)`-tensor's covariant Hessian; the leading `euclidPartial ∘ euclidPartial`
of `h`'s component is the genuine chart Hessian `∂²h`. -/
theorem chartCovariantSecondGrad_chartHessian_sub_correction
    (g : SmoothRiemannianMetric I M) (h : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g 0 (2 + 2)
        (iteratedCovGrad (I := I) g 0 2 2 h) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (fun y' =>
            euclidPartial (E := E) ((Matrix.vecTail Jdx) 0)
                (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2
                  h α Idx (Matrix.vecTail (Matrix.vecTail Jdx)))) y'
              + covDerivLowerOrderTerm (I := I) (M := M) g 0 2 h α
                  ((Matrix.vecTail Jdx) 0) Idx
                  (Matrix.vecTail (Matrix.vecTail Jdx)) y') y
        + covDerivLowerOrderTerm (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 h) α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  rw [chartCovariantSecondGrad_eq (I := I) (M := M) g h α Idx Jdx hy]
  have hEqOn : Set.EqOn
      (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 h) α Idx (Matrix.vecTail Jdx)))
      (fun y' =>
        euclidPartial (E := E) ((Matrix.vecTail Jdx) 0)
            (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2
              h α Idx (Matrix.vecTail (Matrix.vecTail Jdx)))) y'
          + covDerivLowerOrderTerm (I := I) (M := M) g 0 2 h α
              ((Matrix.vecTail Jdx) 0) Idx
              (Matrix.vecTail (Matrix.vecTail Jdx)) y')
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y' hy'
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy']
    exact chartCovariantSecondGrad_inner (I := I) (M := M) g h α Idx
      (Matrix.vecTail Jdx) hy'
  have hEv := Filter.eventuallyEq_of_mem
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy) hEqOn
  congr 1
  rw [euclidPartial_def, euclidPartial_def, hEv.fderiv_eq]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
