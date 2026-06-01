import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerUpperBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge

/-!
# Bundle-fibre upper bound for the `(r, s)` pointwise inner product

This file bridges the chart-frame quadratic upper bound established in
`ChartTensorInnerUpperBound.lean` to the bundle-fibre `(r, s)` pointwise
inner product `tensorInnerPointwise`. The bridge identity
`chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise` from
`ChartTensorInnerBridge.lean` identifies the chart-frame diagonal value
at a model tensor `T` with the bundle-fibre diagonal value at the
chart-`(α, b)`-twisted tensor `chartRSTwist α b r s T`.

Composing the upper bound with the bridge produces, on the closed support
of the chart-atlas partition-of-unity weight at `α`, a uniform-in-`b`
inequality of the form

`tensorInnerPointwise g r s b (chartRSTwist α b r s T) (chartRSTwist α b r s T) ≤
  C * ‖T‖^2`

for every model `(r, s)`-tensor `T`. Substituting `T = chartRSTwistInv α b r s S`
and using the round-trip identity
`chartRSTwist α b r s (chartRSTwistInv α b r s S) = S` (valid on the chart
base set) yields the directly usable bundle-fibre form

`tensorInnerPointwise g r s b S S ≤ C * ‖chartRSTwistInv α b r s S‖^2`.

Specialising further to `S = S.toFun b` for a smooth compactly-supported
`(r, s)`-tensor section `S`, and identifying
`chartRSTwistInv α b r s (S.toFun b) = tensorTrivProj g r s S α b` via
`tensorTrivProj_eq_chartRSTwistInv_toFun`, gives the trivialisation-based
form

`tensorInnerPointwise g r s b (S.toFun b) (S.toFun b) ≤ C * ‖tensorTrivProj g r s S α b‖^2`.

## Main results

* `exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport`
  — the chart-frame composed bound: a uniform `C` controls the bundle-
  fibre diagonal value on the chart-`(α, b)`-twisted tensor by the
  squared norm of the untwisted model tensor.
* `exists_tensorInnerPointwise_upper_bound_via_chartRSTwistInv_norm_sq_on_pouTsupport`
  — equivalent form by the chart-`(α, b)`-twist round-trip: the bundle-
  fibre diagonal value at a model tensor is controlled by the squared
  norm of its `chartRSTwistInv`-image.
* `exists_tensorInnerPointwise_upper_bound_via_trivProj_norm_sq_on_pouTsupport`
  — bundle-fibre flavour at a smooth compactly-supported section: the
  diagonal value at `S.toFun b` is controlled by the squared norm of the
  trivialisation projection `tensorTrivProj g r s S α b`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

section UpperBoundViaTwist

/-- **Chart-twist composed upper bound for the bundle-fibre `(r, s)`-inner
product diagonal**.

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and ranks
`(r, s)`, there is a non-negative constant `C` such that, for every `b` in
the closed support of the chart-atlas partition-of-unity weight at `α` and
every model `(r, s)`-tensor `T`,
`tensorInnerPointwise g r s b (chartRSTwist α b r s T) (chartRSTwist α b r s T)
  ≤ C * ‖T‖^2`.

Proof: the bridge identity
`chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise` rewrites the
chart-frame diagonal quadratic value as the bundle-fibre diagonal value on
the chart-`(α, b)`-twisted tensor. The chart-frame upper bound
`exists_chartTensorInnerPointwise_rs_model_upper_bound_on_pouTsupport`
provides the desired inequality on the chart-frame side, and the bridge
transfers it to the bundle-fibre side. -/
theorem exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          tensorInnerPointwise (I := I) (M := M) g r s b
              (chartRSTwist (I := I) (M := M) α b r s T)
              (chartRSTwist (I := I) (M := M) α b r s T) ≤
            C * ‖T‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_chart⟩ :=
    exists_chartTensorInnerPointwise_rs_model_upper_bound_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro b hb T
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have h := h_chart b hb T
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T] at h
  exact h

/-- **Round-tripped bundle-fibre upper bound (chartRSTwistInv form)**.

Substituting `T = chartRSTwistInv α b r s S` into the chart-twist composed
upper bound and using the round-trip identity
`chartRSTwist α b r s (chartRSTwistInv α b r s S) = S` (valid on the chart
base set) yields the bundle-fibre diagonal value at `S` controlled by the
squared norm of its `chartRSTwistInv`-image.

This is the form most directly comparable to the lower-bound headline
`chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport`
in `NormComparison.lean`. -/
theorem exists_tensorInnerPointwise_upper_bound_via_chartRSTwistInv_norm_sq_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ S : TensorRSModel r s ℝ E,
          tensorInnerPointwise (I := I) (M := M) g r s b S S ≤
            C * ‖chartRSTwistInv (I := I) (M := M) α b r s S‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_twist⟩ :=
    exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro b hb S
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  set T : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s S with hT_def
  have h_round : chartRSTwist (I := I) (M := M) α b r s T = S := by
    rw [hT_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s S
  have h := h_twist b hb T
  rw [h_round] at h
  exact h

end UpperBoundViaTwist

section UpperBoundViaTrivProj

/-- **Bundle-fibre upper bound via the trivialisation projection of a smooth
compactly-supported `(r, s)`-tensor section.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, ranks
`(r, s)`, and any smooth compactly-supported `(r, s)`-tensor section `S`,
there is a non-negative constant `C` (independent of `S`) such that, for
every `b` in the closed support of the chart-atlas partition-of-unity
weight at `α`,
`tensorInnerPointwise g r s b (S.toFun b) (S.toFun b) ≤
  C * ‖tensorTrivProj g r s S α b‖^2`.

Proof: instantiate the chartRSTwistInv-form bound at `S = S.toFun b` and
rewrite the RHS using `tensorTrivProj_eq_chartRSTwistInv_toFun` to
`tensorTrivProj g r s S α b = chartRSTwistInv α b r s (S.toFun b)`. -/
theorem exists_tensorInnerPointwise_upper_bound_via_trivProj_norm_sq_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        b ∈ tsupport (fun x : M =>
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) ≤
            C * ‖tensorTrivProj (I := I) (M := M) (E := E) g r s S α b‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_inv⟩ :=
    exists_tensorInnerPointwise_upper_bound_via_chartRSTwistInv_norm_sq_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have h := h_inv b hb (S.toFun b)
  have h_proj := tensorTrivProj_eq_chartRSTwistInv_toFun
    (I := I) (M := M) g r s α S hb_base
  rw [← h_proj] at h
  exact h

end UpperBoundViaTrivProj

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
