import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity

/-!
# The chart-Gram difference of two realized metrics is the realized tensor difference

The crux analytic step of the geometric Ricci–DeTurck nonlinearity construction
bounds the chart `2`-jet seminorm `chartMetricJet2DiffSup (realizeMetricAt u₁)
(realizeMetricAt u₂)` of the difference of the two realized metrics by the
intrinsic `H^{a+1}` spectral norm of `u₁ − u₂`.  Its **algebraic entry point** is
the observation that the chart-Gram difference of the two realized metrics is the
chart-frame component of the *realized symmetric bilinear form of the tensor
difference* `T₁ − T₂`, with `Tₖ` the smooth representative of `uₖ`.  This file
records that reduction.

Concretely, on the joint validity domain (both `uₖ` finitely supported and
fibre-small, so both realized metrics are honest), for every chart base point `α`
and every base point `x` in the chart-`α` base set,

  `g₁.inner x v w − g₂.inner x v w
     = ccTensorBilinSymm g_bg (T₁ − T₂) x v w`,

where `g_k = realizeMetricAt g_bg u_k`.  This holds because each realized metric is
fibrewise `g_bg + ccTensorBilinSymm g_bg T_k`, the `g_bg` summands cancel in the
difference, and `ccTensorBilinSymm` is additive (subtractive) in the tensor
section.

The chart-Gram matrix entry is the value of the metric inner product on the chart
basis frame, so the chart-Gram difference entry is exactly the realized symmetric
form of `T₁ − T₂` on that frame.  This identifies the chart `0`-, `1`-, `2`-jets
of the metric difference with the chart-coordinate jets of the chart components of
the *fixed* `(0,2)`-tensor section `T₁ − T₂`, which is the object the intrinsic
covariant Sobolev / `C²` embedding controls.

## Sign convention

Geometer `Δ_∇ = −∇*∇`; resolvent `(1 − Δ_∇)⁻¹`, weights `(1 + λᵢ)^σ ≥ 1` for
`σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The underlying multilinear field `ccTensorMultilinear` is subtractive in the
tensor section. -/
theorem ccTensorMultilinear_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (S - T) x : Tensor0SSpace 2 I x)
      = (ccTensorMultilinear (I := I) g S x : Tensor0SSpace 2 I x)
        - (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_sub]
  change ((S.toSection - T.toSection) x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    = (S.toSection x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      - (T.toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply]

/-- The model value `ccTensorModel` is subtractive in the tensor section. -/
theorem ccTensorModel_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (S - T) x =
      ccTensorModel (I := I) g S x - ccTensorModel (I := I) g T x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_sub, Tensor0SSpace.toModel_sub]

/-- The extracted bilinear form `ccTensorBilin` is subtractive in the tensor
section. -/
theorem ccTensorBilin_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (S - T) x v w =
      ccTensorBilin (I := I) g S x v w - ccTensorBilin (I := I) g T x v w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply,
    ccTensorModel_sub, ContinuousMultilinearMap.sub_apply]

/-- The symmetrized extracted bilinear form `ccTensorBilinSymm` is subtractive in
the tensor section. -/
theorem ccTensorBilinSymm_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S - T) x v w =
      ccTensorBilinSymm (I := I) g S x v w -
        ccTensorBilinSymm (I := I) g T x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_sub]
  ring

/-- The smooth representative of a realizable element `u`, chosen via the finite
support witness packaged in `realizableAt`. -/
def realizableRepr (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu : realizableAt (I := I) g_bg u) :
    SmoothCcTensor g_bg 0 2 :=
  Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
    (I := I) (M := M) u hu.choose

/-- On the validity domain, the realized metric's inner product is `g_bg` plus the
symmetrized extracted form of the smooth representative. -/
theorem realizeMetricAt_inner_eq_repr (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu : realizableAt (I := I) g_bg u) (x : M) (v w : TangentSpace I x) :
    (realizeMetricAt (I := I) g_bg u).inner x v w =
      g_bg.inner x v w +
        ccTensorBilinSymm (I := I) g_bg (realizableRepr (I := I) g_bg hu) x v w := by
  classical
  obtain ⟨hu_fs, δ', hδ'_lt, hδ'⟩ := id hu
  rw [realizeMetricAt_inner_of_realizable (I := I) g_bg u hu_fs hδ'_lt hδ' x v w]
  rfl

/-- **The chart-Gram difference of two realized metrics is the realized symmetric
form of the tensor difference.**

For two realizable order-`σ` elements `u₁, u₂` (smooth representatives `T₁, T₂`),
the chart-Gram matrix entry difference of the two realized metrics
`g_k = realizeMetricAt g_bg u_k`, in any chart `α` at any base point `x`, is the
symmetrized extracted bilinear form of the *fixed* `(0,2)`-tensor section
`T₁ − T₂` on the chart-`α` basis frame:

  `G_{ij}(g₁)(α, x) − G_{ij}(g₂)(α, x)
     = ccTensorBilinSymm g_bg (T₁ − T₂) x (e_i^α x) (e_j^α x)`.

The `g_bg` summands of the two realized inner products cancel, and
`ccTensorBilinSymm` is subtractive in the tensor section.  This identifies the
chart `0`-jet (and, by differentiating in the chart coordinate, all higher chart
jets) of the metric difference with the chart-coordinate jets of the chart
components of the single tensor section `T₁ − T₂` — the object on which the
intrinsic covariant Sobolev / `C²` embedding gives uniform control. -/
theorem chartGramMatrix_realizeMetricAt_sub_eq_reprDiff
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α x i j -
        chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α x i j =
      ccTensorBilinSymm (I := I) g_bg
        (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) := by
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    realizeMetricAt_inner_eq_repr (I := I) g_bg hu₁ x _ _,
    realizeMetricAt_inner_eq_repr (I := I) g_bg hu₂ x _ _,
    ccTensorBilinSymm_sub]
  ring

/-- The chart-Gram-on-`E` difference of two realized metrics at a chart point `y`
is the realized symmetric form of the tensor difference, evaluated at the chart
preimage `(extChartAt I α).symm y`. -/
theorem chartGramOnE_realizeMetricAt_sub_eq_reprDiff
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α i j y -
        chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α i j y =
      ccTensorBilinSymm (I := I) g_bg
        (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
        ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)) := by
  rw [chartGramOnE_def, chartGramOnE_def]
  exact chartGramMatrix_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂ α _ i j

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
