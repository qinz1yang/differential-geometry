import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGradMetricBridge

/-!
# The covariant-gradient `L²` inner product as the integrated Dirichlet pairing

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, fixed ranks `(r, s)`, and two smooth
compactly-supported `(r, s)`-tensor sections `T`, `v`, this file ships the
*off-diagonal* metric-isometry identity, in integrated form:

```
tensorL2Inner g r (s + 1) (covGrad g r s T).toFun (covGrad g r s v).toFun
  = ∫ x, tensorCovDerivPointwiseInner g r s T v x ∂(riemannianVolumeMeasure g).
```

The `(r, s + 1)`-tensor `L²` inner product of the two section-level covariant
gradients equals the integral of the pointwise inverse-Gram-weighted
covariant-gradient (Dirichlet) pairing. It is the polarised form of the
diagonal Dirichlet identity, obtained by integrating the pointwise
metric-isometry bridge
`tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad` against the
Riemannian volume measure. No hypothesis on `T`, `v`, or the metric beyond the
standing closed-manifold typeclasses is required.

This is the gradient-side (`LHS`) bridge of the integrated Green identity for
the connection Laplacian: it converts the headline left-hand side, written with
the one-rank-higher `L²` inner product of covariant gradients, into the
integrated Dirichlet pairing that the directional integration-by-parts
machinery consumes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The off-diagonal covariant-gradient `L²` inner product is the integrated
Dirichlet pairing.**

For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, and two smooth
compactly-supported `(r, s)`-tensor sections `T`, `v`, the one-rank-higher
`(r, s + 1)`-tensor `L²` inner product of the section-level covariant gradients
`covGrad g r s T` and `covGrad g r s v` equals the integral of the pointwise
covariant-gradient inner product `tensorCovDerivPointwiseInner g r s T v`:

```
tensorL2Inner g r (s + 1) (covGrad g r s T).toFun (covGrad g r s v).toFun
  = ∫ x, tensorCovDerivPointwiseInner g r s T v x ∂(riemannianVolumeMeasure g).
```

The identity is the integral of the pointwise metric-isometry bridge
`tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad`, applied with the
two distinct sections `T`, `v`. It is the polarised generalisation of the
diagonal Dirichlet identity. -/
theorem tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T).toFun
        (covGrad (I := I) (M := M) g r s v).toFun =
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  change tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s T).toSection x))
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s v).toSection x)) =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
  exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s T v x).symm

end Connection
end Integral
end DifferentialGeometry

end
