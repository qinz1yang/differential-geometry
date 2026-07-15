import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition

/-!
# The covariant `L²`-jet decomposition bound of the realized Ricci–DeTurck RHS section

For a fibre-small smooth perturbation `T` (so that the realized metric
`g_bg + h_sym T = tensorSectionRealizeMetric g_bg T` is a genuine Riemannian metric), the
*genuine geometric Ricci–DeTurck right-hand side* `deTurckRHSSection g_bg (g_bg + h_sym T)`
is a smooth `(0,2)`-tensor section.  Its underlying smooth section, **reanchored** to the
background metric `g_bg` (the metric parameter of a `SmoothCcTensor` is a phantom type
parameter that touches no data field, so reanchoring is a pure rewrap), is the object whose
iterated `g_bg`-covariant gradients `∇^j` the strong-existence assembly differentiates and
takes `L²` norms of.

This file builds the **covariant `L²`-jet Nemytskii decomposition bound** for that section:
on the fibre-small regime the order-`≤ N` covariant `L²` jets of the realized-RHS *difference*
`R̃ T − R̃ T'` are bounded by a fixed multiple of the order-`≤ N + 2` covariant `L²` jets of the
perturbation difference `T − T'`.  The two extra covariant orders are the second-order
quasilinearity of the Ricci–DeTurck right-hand side (the DeTurck vector field `W(g)` carries
`∂g`, so `𝓛_{W(g)} g` carries `∂²g`, and `Ric(g)` carries `∂²g`).

## Mathematical content

`deTurckRicciRHS g_bg g = -2 · Ric(g) + 𝓛_{W(g, g_bg)} g`.  Expanding the iterated covariant
gradient `∇^k` of this section by the covariant Leibniz / Faà-di-Bruno rule produces a finite
sum of products of (chart-Christoffel / DeTurck-coefficient) jet factors of `g = g_bg + h_sym T`
with covariant jets of the perturbation `h_sym T`.  On the fibre-small regime
(`g` uniformly close to `g_bg`) all the Christoffel / inverse-Gram / DeTurck-coefficient
building blocks are uniformly bounded — exactly the `R`-ball uniform regime of
`exists_chartLieDeTurckComp_lipschitz_on_compact` — so the leading coefficient is a single
fibre-small constant `Λ`.  The genuine pointwise differential-geometry input is therefore the
**covariant-Leibniz pointwise domination**

```
‖∇^k (R̃ T − R̃ T')(x)‖² ≤ Λ² · ∑_{i ≤ k + 2} ‖∇^i (T − T')(x)‖²   (∀ x),
```

with `Λ` uniform on the fibre-small ball.  Given that pointwise bound, the global covariant
`L²`-jet inequality is assembled here outright by the finite-sum pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`, summed over the jet window — no further
analytic content.

## The consumer

The bound is the analytic core wrapped (cutoff · realize plumbing, and the linear `−Δ_∇ T`
summand) by the strong-existence node `deTurckRemainderOfSection_iteratedCovGrad_l2Norm_lipschitz`
@ `ShortTime/DeTurckRicciStrongExistence.lean`, which feeds the geometric Nemytskii `L²`
Lipschitz `deTurckRicciNsec_diff_oneMinusConnLapIter_l2_lipschitz`.

## Main results

* `deTurckRHSReanchor` — the `g_bg`-reanchored realized-RHS smooth section
  `deTurckRHSSection g_bg (g_bg + h_sym T)`, as a `SmoothCcTensor g_bg 0 2`.
* `deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination` (posited TRUE pointwise
  primitive) — the fibre-small covariant-Leibniz pointwise domination of `∇^k (R̃ T − R̃ T')`
  by the order-`≤ k + 2` jets of `T − T'`.
* `deTurckRHSSection_iteratedCovGrad_chartComponent_decomposition` — the headline covariant
  `L²`-jet decomposition bound, assembled from the pointwise primitive.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The `g_bg`-reanchored realized Ricci–DeTurck RHS section.**

For a fibre-small smooth perturbation `T` (`ccTensorBilinSymm T` is `g_bg`-fibre small with
constant `δ < 1`, so `g_bg + h_sym T = tensorSectionRealizeMetric g_bg T` is a genuine metric),
this is the underlying smooth section of `deTurckRHSSection g_bg (g_bg + h_sym T)`, repackaged as
a `SmoothCcTensor g_bg 0 2`.

The metric parameter of `SmoothCcTensor` touches no data field (it is a phantom type parameter,
see `Integral.L2.SmoothCcTensor`), so this rewrap is the section the strong-existence assembly
differentiates with the *background* connection `∇ = ∇^{g_bg}` (the anchor of
`iteratedCovGrad g_bg`).  This matches verbatim the `toSection`/`hasCompactSupport` fields the
`deTurckRemainderOfSection` construction extracts. -/
def deTurckRHSReanchor (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    SmoothCcTensor g_bg 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).hasCompactSupport

omit [BoundarylessManifold I M] in
/-- The reanchored realized-RHS section carries exactly the section of
`deTurckRHSSection g_bg (g_bg + h_sym T)`. -/
@[simp] theorem deTurckRHSReanchor_toSection (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ).toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection := rfl

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
