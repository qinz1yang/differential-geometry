import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.NormComparison
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Inner
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric

/-!
# Uniform pointwise norm comparison for `(r, s + 1)`-tensors

The gradient of a smooth `(r, s)`-tensor section is naturally a smooth
`(r, s + 1)`-tensor section. Consequently, the uniform pointwise norm
comparison delivered for general `(r, s)` in `NormComparison.lean`
specialises at index pair `(r, s + 1)` to produce the corresponding
estimate suitable for application to the gradient tensor.

This file packages that specialisation as standalone headline theorems
and records the bridge identity (chart-frame `↔` bundle-fibre via
`chartRSTwist`) in the gradient-indexed form as well. No new
infrastructure is required: every result here is a direct invocation of
the parent statement at the shifted index `(r, s + 1)`, exposed under a
gradient-flavoured name so that downstream parabolic / Bochner files can
consume it without re-indexing.

## Main results

* `chartTrivializationNorm_grad_le_const_mul_chartTensorInnerPointwise_rs_succ_model_on_pouTsupport`
  — for ranks `(r, s)`, the Euclidean square norm of any
  `(r, s + 1)`-model tensor is bounded by a non-negative constant times
  the chart-frame `(r, s + 1)`-diagonal quadratic form, uniformly on the
  closed support of the chart-atlas partition-of-unity weight at the
  chart base point `α`.
* `chartTrivializationNorm_grad_le_const_mul_tensorInnerPointwise_chartRSTwist_succ_on_pouTsupport`
  — the bundle-fibre form: the same comparison with the chart-frame
  quadratic form replaced by the bundle-fibre `(r, s + 1)`-inner product
  on the chart-`(α, b)`-twisted tensor, obtained from the chart-frame
  form via the bridge identity
  `chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise` at index
  pair `(r, s + 1)`.

Both theorems carry the same closed-manifold hypotheses as their
generic-`(r, s)` parents: `[CompactSpace M]`, `[I.Boundaryless]`,
`[T2Space M]`, `[SigmaCompactSpace M]`, `[InnerProductSpace ℝ E]`, and
`[NeZero (Module.finrank ℝ E)]`. The latter ensures `Tensor0SModel n ℝ E`
is non-zero for every `n`, which is what the unit-sphere lower bound
argument needs.

## Strategy

Pure specialisation. Group A's
`chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport`
is universally quantified over `(r, s : ℕ)`. Setting `s ↦ s + 1` gives
the headline theorem here directly. The bundle-fibre version is the
analogous specialisation of
`chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport`.

The interpretation of `TensorRSModel r (s + 1) ℝ E` as the model fibre
of the gradient bundle requires an explicit isomorphism between the
`(r, s + 1)`-tensor bundle and the gradient bundle
`Hom(TM, (r, s)-tensor bundle)` of a smooth `(r, s)`-tensor section.
That isomorphism is not constructed in this file: this file is the
target norm comparison that any such isomorphism will plug into. The
bridge to `tensorCovDerivPointwiseInner` proceeds via a per-rank
isomorphism downstream, and this file's deliverable is precisely the
ingredient that bridge needs.

## Cross-rank consistency

The shifted-index theorems carry a hidden `(r + (s + 1))` in the
underlying chart-frame `(0, n)`-inner product, exactly as their parents
carry `(r + s)`. No new lemmas about `r + (s + 1) = r + s + 1` are
needed: the parent statements abstract over the dimension count and we
inherit their proof.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section HeadlineGradientNormComparison

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-- **Gradient-indexed headline pointwise norm comparison (chart-frame
form).**

For ranks `(r, s)`, the Euclidean square norm of any
`(r, s + 1)`-model tensor is bounded above by a non-negative constant
`K` times the chart-frame `(r, s + 1)`-diagonal quadratic form,
uniformly on the closed support of the chart-atlas partition-of-unity
weight at the chart base point `α`.

This is the gradient-flavoured specialisation: the gradient of a smooth
`(r, s)`-tensor section is a smooth `(r, s + 1)`-tensor section, so the
present statement is what controls the chart-frame square norm of any
gradient model tensor in terms of its diagonal quadratic form.

The proof is pure specialisation: invoke
`chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport`
with the second index set to `s + 1`. -/
theorem
    chartTrivializationNorm_grad_le_const_mul_chartTensorInnerPointwise_rs_succ_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r (s + 1) α b T T :=
  chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (I := I) (M := M) g r (s + 1) α

/-- **Gradient-indexed headline pointwise norm comparison (bundle-fibre
form, via the chart-`(α, b)`-twist).**

The model-tensor Euclidean square norm of any `(r, s + 1)`-model tensor
is bounded above by a non-negative constant `K` times the bundle-fibre
`(r, s + 1)`-inner product on the chart-`(α, b)`-twisted tensor,
uniformly on the closed support of the chart-atlas partition-of-unity
weight at `α`.

This is the gradient-flavoured specialisation of
`chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport`,
obtained by setting the second index to `s + 1`. -/
theorem
    chartTrivializationNorm_grad_le_const_mul_tensorInnerPointwise_chartRSTwist_succ_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T)
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T) :=
  chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport
    (I := I) (M := M) g r (s + 1) α

/-- Non-negativity of the bundle-fibre `(r, s + 1)`-inner product on the
diagonal at the chart-`(α, b)`-twisted tensor, on the chart base set.
This is the gradient-indexed packaging of
`chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise` combined
with `chartTensorInnerPointwise_rs_model_nonneg`. -/
lemma tensorInnerPointwise_chartRSTwist_succ_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSModel r (s + 1) ℝ E) :
    0 ≤ tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
      (chartRSTwist (I := I) (M := M) α b r (s + 1) T)
      (chartRSTwist (I := I) (M := M) α b r (s + 1) T) := by
  have hbridge :=
    chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r (s + 1) α hb T T
  rw [← hbridge]
  exact chartTensorInnerPointwise_rs_model_nonneg
    (I := I) (M := M) g r (s + 1) α hb T

end HeadlineGradientNormComparison

section CombinedGradient

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-- A single non-negative constant `K` such that both the `(r, s)`- and
`(r, s + 1)`-pointwise norm comparisons hold uniformly on the closed
support of the chart-atlas partition-of-unity weight at `α`. Useful as a
one-step entry point when the consumer needs to bound *both* a
section's chart-frame square norm and its gradient's chart-frame square
norm at the same point. -/
theorem
    chartTrivializationNorm_section_and_grad_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T) ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r (s + 1) α b T T) := by
  classical
  obtain ⟨K₀, hK₀_nn, h₀⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) g r s α
  obtain ⟨K₁, hK₁_nn, h₁⟩ :=
    chartTrivializationNorm_grad_le_const_mul_chartTensorInnerPointwise_rs_succ_model_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K₀ + K₁, add_nonneg hK₀_nn hK₁_nn, ?_, ?_⟩
  · intro b hb T
    have h := h₀ b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hQ_nn : 0 ≤ chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T T :=
      chartTensorInnerPointwise_rs_model_nonneg
        (I := I) (M := M) g r s α hb_base T
    have hineq : K₀ * chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T T ≤
        (K₀ + K₁) * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T :=
      mul_le_mul_of_nonneg_right
        (by linarith : K₀ ≤ K₀ + K₁) hQ_nn
    linarith
  · intro b hb T
    have h := h₁ b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hQ_nn : 0 ≤ chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r (s + 1) α b T T :=
      chartTensorInnerPointwise_rs_model_nonneg
        (I := I) (M := M) g r (s + 1) α hb_base T
    have hineq : K₁ * chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r (s + 1) α b T T ≤
        (K₀ + K₁) * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r (s + 1) α b T T :=
      mul_le_mul_of_nonneg_right
        (by linarith : K₁ ≤ K₀ + K₁) hQ_nn
    linarith

/-- The bundle-fibre variant of the combined estimate: a single
non-negative constant `K` controls both the chart-frame square norm of
an `(r, s)`-model tensor and that of an `(r, s + 1)`-model tensor by
the bundle-fibre inner product on the corresponding chart-`(α, b)`-
twisted tensors. -/
theorem
    chartTrivializationNorm_section_and_grad_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r s b
            (chartRSTwist (I := I) (M := M) α b r s T)
            (chartRSTwist (I := I) (M := M) α b r s T)) ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T)
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T)) := by
  classical
  obtain ⟨K, hK_nn, h_sec, h_grad⟩ :=
    chartTrivializationNorm_section_and_grad_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K, hK_nn, ?_, ?_⟩
  · intro b hb T
    have h := h_sec b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
        (I := I) (M := M) g r s α hb_base T T] at h
    exact h
  · intro b hb T
    have h := h_grad b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
        (I := I) (M := M) g r (s + 1) α hb_base T T] at h
    exact h

end CombinedGradient

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
