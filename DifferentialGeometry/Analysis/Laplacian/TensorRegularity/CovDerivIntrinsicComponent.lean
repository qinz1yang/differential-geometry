import DifferentialGeometry.Integral.Connection.ChartTensorRSCurryFactor
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartPrimitives
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.ChristoffelDecomp

/-!
# The intrinsic chart piece of the tensor covariant derivative on a raw component

For a smooth, compactly-supported `(r, s)`-tensor section `S` over a closed
Riemannian manifold `(M, g)` and a chart center `α : M`, the chart-coordinate
covariant derivative `chartTensorRSCovariantDerivative r s g α S.toSection X b`
decomposes (see `ChartTensorRSCovariantDerivative.lean`) as

```
tensorRSIntrinsicChartCLM r s α S.toSection b (X b)
  + ∑ₖ chartTensorRSInputSlotCorrection …
  − ∑ₗ chartTensorRSOutputSlotCorrection …
```

This file isolates the **intrinsic (Fréchet-derivative) piece**
`tensorRSIntrinsicChartCLM` and computes its raw chart-scalar component.

The raw chart-scalar component of an `(r, s)`-tensor section is the
partition-of-unity-unweighted function
`tensorChartComponentRaw g r s S α Idx Jdx : M → ℝ`, the `(Idx, Jdx)`-entry of
the chart-`α`-trivialised model-fibre representation. The headline result of
this file says: projecting the intrinsic chart piece — evaluated along the
`k`-th chart-coordinate basis vector field — to a raw chart-scalar component
yields exactly the `k`-th chart-Euclidean partial derivative `euclidPartial k`
of that raw component (pushed forward to the Euclidean chart target). In other
words, modulo the Christoffel slot-correction terms (handled elsewhere), the
chart-coordinate covariant derivative of a tensor component is the plain chart
partial derivative.

The whole development is phrased on the **raw** component
`tensorChartComponentRaw` (and its push-forward `chartPushedRaw`); the
partition-of-unity weight does not appear.

## Main results

* `tensorRSChartE_section_repr_eq_tensorTrivProj` — the chart-`α`-trivialised
  representation of `S.toSection` coincides with the trivialisation projection
  `tensorTrivProj g r s S α`.
* `tensorRSIntrinsicChartCLM_proj_eq_fderiv_component` — the raw-component
  projection of the trivialised intrinsic chart piece equals the Fréchet
  derivative of the chart-pulled-back raw component.
* `tensorRSIntrinsicChartCLM_component_eq_euclidPartial` — the headline: the
  raw-component projection of the intrinsic chart piece along the `k`-th
  chart-coordinate basis vector equals `euclidPartial k` of the Euclidean
  push-forward of the raw component.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The chart-`α`-trivialised model-fibre representation of the underlying
section of a `SmoothCcTensor` coincides with the trivialisation projection
`tensorTrivProj g r s S α`. Both are
`(trivializationAt …).continuousLinearMapAt ℝ x (S.toSection x)`. -/
theorem tensorRSChartE_section_repr_eq_tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tensorRSChartE_section_repr (I := I) r s α S.toSection =
      tensorTrivProj (I := I) (M := M) g r s S α :=
  rfl

/-- **Raw-component projection of the intrinsic chart piece.** For `b` in the
chart source at `α` whose chart image lies in the interior of the chart target,
and any tangent vector `v`, projecting the trivialised intrinsic chart
Fréchet-derivative value of `S.toSection` along `v` to the `(Idx, Jdx)`-raw
component equals the Fréchet derivative of the chart-pulled-back raw scalar
component `tensorChartComponentRaw g r s S α Idx Jdx ∘ (extChartAt I α).symm`,
evaluated at `extChartAt I α b` in the chart-trivialisation direction
`trivToE α b v`. -/
theorem tensorRSIntrinsicChartCLM_proj_eq_fderiv_component
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source)
    (hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (v : TangentSpace I b) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection b v)) =
      fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b v) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hb_baseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α S.toSection b v]
  unfold tensorRSChartFiberFromModel
  rw [(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
      (R := ℝ) hb_baseRS]
  rw [tensorRSChartE_section_repr_eq_tensorTrivProj (I := I) (M := M) g r s S α]
  rw [tensorChartComponentRaw_partial_decomp (I := I) (M := M) g r s α S
    hb_chart hb_int Idx Jdx (trivToE (I := I) α b v)]

/-- **The intrinsic chart piece is the chart partial derivative.** Let
`y` lie in the chart-Euclidean target `chartTargetEuclid α`, and set
`b := (extChartAt I α).symm (toEuclidean.symm y)`. Then the raw-component
projection of the intrinsic chart Fréchet-derivative piece of `S.toSection`,
evaluated along the `k`-th chart-coordinate basis vector field
`chartBasisVecFiber α k`, equals the `k`-th chart-Euclidean partial derivative
`euclidPartial k` of the Euclidean push-forward
`chartPushedRaw I α (tensorChartComponentRaw g r s S α Idx Jdx)` of the raw
chart-scalar component, evaluated at `y`. -/
theorem tensorRSIntrinsicChartCLM_component_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α k
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))) =
      euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  rw [tensorRSIntrinsicChartCLM_proj_eq_fderiv_component (I := I) (M := M)
    g r s S α Idx Jdx hb_chart hb_int (chartBasisVecFiber (I := I) α k b)]
  have htriv_basis :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α k b) =
        chartModelBasis E k := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b (chartModelBasis E k)) = _
    exact trivToE_trivFromE (I := I) α hb_base (chartModelBasis E k)
  rw [htriv_basis, chartModelBasis_apply, hphi_b]
  rw [euclidPartial_def]
  have hpushed_eq :
      chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) =ᶠ[𝓝 y]
        ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hz
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
      (extChartAt I α).symm) (x := y)]
  rfl

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
