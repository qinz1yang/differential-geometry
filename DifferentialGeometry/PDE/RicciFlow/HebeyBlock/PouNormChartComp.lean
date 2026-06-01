import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.UniformChartBounds
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

/-- Two-sided norm equivalence between the chart-aggregated partition-of-
unity-weighted Hilbert-Schmidt chart-Sobolev norm
`(tensorPouSobolevHsNorm g 0 T).toReal`, which underlies the inner-product
structure on the intrinsic `H^0` Hilbert space `TensorPouSobolevHilbert
g r s 0` (via `tensorPouSobolevHilbert_norm_eq`), and the operator-norm
counterpart `(tensorPouSobolevNorm g 0 T).toReal`.

# Blueprint intent

The intrinsic `H^0` Hilbert-space norm on `TensorPouSobolevHilbert g r s 0`
is induced by the **Hilbert-Schmidt** chart-aggregated norm
`(tensorPouSobolevHsNorm g 0 T).toReal`, which collects the chart-frame
component squared moduli of `T` summed against the partition-of-unity.
The **operator-norm** counterpart `(tensorPouSobolevNorm g 0 T).toReal`
is the analogous chart-aggregated norm built from the operator norms of
the iterated Fréchet derivatives of the chart-frame components rather
than from their pointwise Hilbert-Schmidt sums of squares.

On finite-dimensional fibres these two aggregation styles differ only by a
**dimension-dependent constant**, hence are equivalent up to constants
depending only on the model fibre dimension and the chart-atlas
partition-of-unity finite support. On a closed manifold this yields a
two-sided global comparison

```
c · (tensorPouSobolevNorm g 0 T).toReal ≤
    (tensorPouSobolevHsNorm g 0 T).toReal ≤
  C · (tensorPouSobolevNorm g 0 T).toReal,
```

valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
with `0 < c ≤ C` depending only on `g`, `r`, `s`, and the dimension of the
model fibre via the Gram-twist constants of `fibrewise_gram_twist_estimate`
absorbed into a single absolute constant through
`uniform_chart_bounds_from_compactness`.

This bridges the operator-norm chart-Sobolev formalism used by
`tensorPouSobolevNorm` with the Hilbert-Schmidt chart-Sobolev formalism
that underlies the inner-product structure on `TensorPouSobolevHilbert`. -/
theorem pou_weighted_norm_equals_chart_component_norm_up_to_constant
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal :=
  fibrewise_gram_twist_estimate (I := I) (M := M) g r s

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
