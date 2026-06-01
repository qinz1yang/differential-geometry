import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.L2BanachIso
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.Rellich
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChartFrameNorm
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.NablaTensorFormula
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.IteratedNabla
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.UniformChartBounds
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.PouNormChartComp
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.AssemblePouIso

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Two-sided norm equivalence at order `k = 1` between the chart-aggregated
operator-norm chart-Sobolev norm `(tensorPouSobolevNorm g 1 T).toReal`,
which is constructed from iterated **partial** derivatives of the
chart-frame scalar components of `T`, and the chart-aggregated
Hilbert-Schmidt chart-Sobolev norm `(tensorPouSobolevHsNorm g 1 T).toReal`,
which underlies the inner-product structure on the intrinsic Hilbert
space `TensorPouSobolevHilbert g r s 1` and is the chart-frame
Hilbert-Schmidt reconstruction of the **intrinsic** iterated covariant
derivative `∇ T`.

# Blueprint intent

This is the chart-Sobolev / intrinsic-`∇` identification at the `H^1`
level. The intrinsic Hilbert space `TensorPouSobolevHilbert g r s 1`
carries the inner-product structure induced by
`tensorPouSobolevHilbert_norm_eq` from the Hilbert-Schmidt chart-Sobolev
norm. On the other side, downstream parabolic / spectral consumers
(`H1Compl`, `L2BanachIso`, `Rellich`, and ultimately the heat-semigroup
calculus) phrase their estimates against the operator-norm chart-Sobolev
norm built from partial derivatives in chart coordinates. Composing the
chart-component / partial-derivative comparison
`iterated_nabla_vs_iterated_partial_equivalence_H1` (`k = 1` instance)
with the order-zero fibrewise Gram-twist comparison
`pou_weighted_norm_equals_chart_component_norm_up_to_constant` and
uniformising all chart-dependent constants through
`uniform_chart_bounds_from_compactness` yields the two-sided global
comparison
```
c · (tensorPouSobolevNorm g 1 T).toReal ≤
    (tensorPouSobolevHsNorm g 1 T).toReal ≤
  C · (tensorPouSobolevNorm g 1 T).toReal,
```
valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
with `0 < c ≤ C` depending only on `g`, `r`, `s`, and the dimension of
the model fibre. This identifies the partial-derivative chart-Sobolev
formalism used in the downstream spectral analysis with the intrinsic
covariant-derivative formalism used in the `H^1` Hilbert-space
construction, establishing the bridge required to identify the spectral
chart-Sobolev space at order `k = 1` with the intrinsic `H^1` Hilbert
space at the level of tensor sections. -/
theorem chart_sobolev_intrinsic_nabla_equivalence_tensors_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
  assemble_pou_h1_iso_intrinsic_h1 (I := I) (M := M) g r s

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
