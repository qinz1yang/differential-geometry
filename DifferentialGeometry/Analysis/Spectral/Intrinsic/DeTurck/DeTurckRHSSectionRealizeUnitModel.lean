import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize

/-! # Unit-model value of the realized Ricci–DeTurck right-hand-side section

The nonlinear Ricci–DeTurck right-hand-side arm of the sealed remainder is, at the section level,
`deTurckRHSSection g_bg (tensorSectionRealizeMetric g₀ T hδ_lt hδ)` — the genuine Ricci–DeTurck
right-hand side `deTurckRicciRHS g_bg (g₀ + T) = −2 Ric(g₀+T) + 𝓛_{W(g₀+T, g_bg)}(g₀+T)` of the
realized metric, packaged as a smooth compactly-supported `(0, 2)`-tensor.  Downstream, the
linearization step reads this arm off in the `unitModel` idiom (the unit-evaluated model `(0, 2)`-form
`unitModel g₀ 2 W x = Tensor0SSpace.toModel (W.toSection x (unit))`), so that a pointwise `unitModel`
equality can be lifted to a genuine `SmoothCcTensor` equality via the extensionality bridge
`smoothCcTensor_ext_of_unitModel`.

This file is the section → pointwise bilinear value bridge: it evaluates the realized
right-hand-side section, in the `unitModel` form, to the pointwise bilinear value `deTurckRicciRHS`.
The proof is the unit-evaluation `deTurckRHSSection_toModel_apply` (`unitTensor x` is, by `rfl`, the
canonical unit `(0, 0)`-tensor `constOfIsEmpty 1`), so the deep curvature/Lie/inverse-Gram content
lives entirely in `deTurckRicciRHS`, ready to be expanded pointwise by the proven Palatini/Koszul/Lie
calculus and then re-packaged.

The arm is carried downstream as a `SmoothCcTensor g₀ 0 2` re-tagged to `g₀` (the phantom metric
parameter does not appear in the underlying section data), while `deTurckRHSSection g_bg g` is tagged to
its realized argument `g`; the bridge is therefore phrased for any `g₀`-tagged section whose underlying
`toSection` agrees with the realized right-hand-side section (the re-tag is `rfl`-cost-free, so a
consumer holding the `g₀`-tagged arm discharges the agreement hypothesis by `rfl`). -/

noncomputable section

open Bundle Tensor0SBundle Manifold
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The unit-model value of the realized Ricci–DeTurck right-hand-side section is the
Ricci–DeTurck bilinear value.**

For any `g₀`-tagged smooth compactly-supported `(0, 2)`-tensor `W` whose underlying section agrees
with the realized right-hand-side section `deTurckRHSSection g_bg (tensorSectionRealizeMetric g₀ T …)`,
the unit-evaluated model `(0, 2)`-form of `W` at `x`, read on a tangent pair `v`, recovers the
Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg (g₀ + T) x (v 0) (v 1)`.

The agreement hypothesis `hW` is `rfl`-discharged by the nonlinear RHS arm `deTurckRHSArmG0`, whose
`toSection` field is, by definition, the realized right-hand-side section: the metric tag on
`SmoothCcTensor` is a phantom parameter, so re-tagging the realized section to `g₀` does not change the
underlying section data.  The proof unfolds `unitModel` to the unit evaluation
`Tensor0SSpace.toModel (W.toSection x (unit))`, rewrites along `hW`, and applies
`deTurckRHSSection_toModel_apply` (with `unitTensor x = constOfIsEmpty 1` by `rfl`). -/
theorem unitModel_of_deTurckRHSSection_realize
    (g₀ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (W : SmoothCcTensor g₀ 0 2)
    (hW : W.toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 W x v =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1) := by
  rw [unitModel]
  change Tensor0SSpace.toModel ((W.toSection x) _) v = _
  rw [hW]
  exact deTurckRHSSection_toModel_apply (I := I) g_bg
    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
