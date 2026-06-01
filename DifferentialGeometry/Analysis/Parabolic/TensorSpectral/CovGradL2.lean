import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGradMetricBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The covariant gradient as a bounded `H¹ → L²` operator on tensor sections

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file packages the section-level covariant
gradient `covGrad g r s` (built in `CovGrad.lean`) as a *bounded linear map*
out of the `H¹` pre-Hilbert space of smooth compactly-supported
`(r, s)`-tensor sections, into the metric `L²` Hilbert space of
one-rank-higher `(r, s + 1)`-tensor sections, and extends it continuously to
the `H¹` Hausdorff completion `TensorH1Compl g r s`.

## Main constructions

* `tensorCovGradL2 g r s` — the covariant gradient of a smooth
  compactly-supported `H¹` tensor section, as a continuous linear map
  `SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r (s + 1) g`.
* `tensorCovGradL2Compl g r s` — the continuous linear extension of
  `tensorCovGradL2 g r s` to the `H¹` completion `TensorH1Compl g r s`.

## Main results

* `tensorCovGradL2Compl_smoothToTensorH1Compl` — on a smooth section the
  completion-extended operator recovers `tensorCovGradL2 g r s`.
* `tensorCovGradL2_inner_smooth` — the smooth-case pairing formula: pairing
  `tensorCovGradL2 g r s w` against (the `L²`-coercion of) a fixed smooth
  `(r, s + 1)`-section `T` equals the integral of the pointwise tensor inner
  product of the section-level covariant gradient `covGrad g r s w.toCcTensor`
  with `T` against the Riemannian volume measure.

## Strategy

The underlying linear map is `w ↦ ((covGrad g r s w.toCcTensor) :
TensorL2 r (s + 1) g)` — the section-level covariant gradient `covGrad`
followed by the canonical `L²` embedding of smooth compactly-supported
sections. It is `ℝ`-linear by `covGrad_add` / `covGrad_smul` together with
linearity of the `SmoothCcTensor → TensorL2` completion embedding.

The operator-norm bound `‖·‖ ≤ 1` is the metric-isometry identity. The
squared `L²` norm of `covGrad g r s w.toCcTensor` is the `L²` self-pairing of
its underlying section, i.e. the integral of the pointwise `(r, s + 1)`-tensor
inner product of the covariant gradient with itself. By the metric-isometry
bridge `tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad` that
integrand coincides, pointwise, with the integrated covariant-gradient
(Dirichlet) term `tensorCovDerivPointwiseInner g r s w.toCcTensor w.toCcTensor`.
The `H¹` inner product `tensorH1Inner` is by definition the `L²` inner product
plus exactly this Dirichlet integral; the `L²` part is non-negative, so the
Dirichlet integral — hence `‖covGrad g r s w.toCcTensor‖²_{L²(s+1)}` — is
bounded above by `‖w‖²_{H¹}`. Thus `‖covGrad g r s w.toCcTensor‖ ≤ ‖w‖`, and
`LinearMap.mkContinuous` with bound `1` assembles the continuous linear map.

The continuous extension to the completion follows the standard pattern: the
embedding `smoothToTensorH1Compl` has dense range and is uniform-inducing, the
codomain `TensorL2 r (s + 1) g` is complete, so `ContinuousLinearMap.extend`
produces the extension and `ContinuousLinearMap.extend_eq` is the
compatibility identity on smooth sections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

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

/-- The `L²` self-pairing of the covariant gradient of a smooth
compactly-supported `(r, s)`-tensor section `S` equals the integral of the
pointwise covariant-gradient inner product `tensorCovDerivPointwiseInner`.

This is the metric-isometry identity, integrated: the genuine
one-rank-higher `L²` self-pairing of `covGrad g r s S` is the integrated
Dirichlet term entering the `H¹` inner product. -/
private lemma tensorL2Inner_covGrad_self_eq_dirichlet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  change tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x))
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x)) =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
  exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s S S x).symm

set_option linter.unusedSectionVars false in
/-- The squared metric `L²` norm of the completion-coercion of the covariant
gradient `covGrad g r s S.toCcTensor` is bounded above by the squared `H¹`
seminorm of `S`. -/
private lemma covGrad_l2NormSq_le_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  have h_coe_norm :
      ‖((covGrad (I := I) (M := M) g r s S.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)‖ =
        ‖(covGrad (I := I) (M := M) g r s S.toCcTensor :
          SmoothCcTensor g r (s + 1))‖ :=
    UniformSpace.Completion.norm_coe _
  rw [h_coe_norm]
  rw [SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
    (covGrad (I := I) (M := M) g r s S.toCcTensor)]
  rw [tensorL2Inner_covGrad_self_eq_dirichlet (I := I) (M := M) g r s S.toCcTensor]
  rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S]
  rw [tensorH1Inner_def]
  have h_l2_nonneg :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
            S.toCcTensor.toFun S.toCcTensor.toFun :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s S.toCcTensor.toFun
  linarith

set_option linter.unusedSectionVars false in
/-- The metric `L²` norm of the completion-coercion of the covariant gradient
`covGrad g r s S.toCcTensor` is bounded above by the `H¹` seminorm of `S`. -/
private lemma covGrad_l2Norm_le_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ≤ ‖S‖ := by
  have h_sq := covGrad_l2NormSq_le_h1NormSq (I := I) (M := M) g r s S
  have h_rhs_nn : 0 ≤ ‖S‖ := norm_nonneg _
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2

set_option linter.unusedSectionVars false in
/-- The bound stated in the `mkContinuous` form: the metric `L²` norm of the
completion-coercion of `covGrad g r s S.toCcTensor` is bounded by
`1 * ‖S‖`. -/
private lemma covGrad_l2Norm_le_one_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]
  exact covGrad_l2Norm_le_h1Norm (I := I) (M := M) g r s S

/-- The `ℝ`-linear map from smooth compactly-supported `H¹` tensor sections to
the one-rank-higher metric `L²` Hilbert space, sending `w` to the metric
`L²`-coercion of the section-level covariant gradient
`covGrad g r s w.toCcTensor`. -/
noncomputable def covGradL2Lin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] TensorL2 r (s + 1) g where
  toFun w :=
    ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
  map_add' w₁ w₂ := by
    change ((covGrad (I := I) (M := M) g r s (w₁ + w₂).toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) =
        ((covGrad (I := I) (M := M) g r s w₁.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) +
          ((covGrad (I := I) (M := M) g r s w₂.toCcTensor :
              SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
    rw [SmoothCcTensorH1.toCcTensor_add,
      covGrad_add (I := I) (M := M) g r s w₁.toCcTensor w₂.toCcTensor]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c w := by
    change ((covGrad (I := I) (M := M) g r s (c • w).toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) =
        c • ((covGrad (I := I) (M := M) g r s w.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
    rw [SmoothCcTensorH1.toCcTensor_smul,
      covGrad_smul (I := I) (M := M) g r s c w.toCcTensor]
    exact UniformSpace.Completion.coe_smul _ _

@[simp] lemma covGradL2Lin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    covGradL2Lin (I := I) (M := M) g r s w =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := rfl

set_option linter.unusedSectionVars false in
/-- Norm bound for the underlying linear map: the metric `L²` norm of
`covGradL2Lin g r s w` is bounded by `1 * ‖w‖`. -/
private lemma covGradL2Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    ‖covGradL2Lin (I := I) (M := M) g r s w‖ ≤ 1 * ‖w‖ := by
  rw [covGradL2Lin_apply]
  exact covGrad_l2Norm_le_one_mul_h1Norm (I := I) (M := M) g r s w

/-- **The covariant gradient as a bounded `H¹ → L²` operator.** The covariant
gradient of a smooth compactly-supported `H¹` tensor section, as a continuous
linear map from the `H¹` pre-Hilbert space of `(r, s)`-tensor sections into
the metric `L²` Hilbert space of one-rank-higher `(r, s + 1)`-tensor sections.

It sends a smooth `H¹` section `w` to the metric `L²`-coercion of the
section-level covariant gradient `covGrad g r s w.toCcTensor`, and has
operator norm bounded by `1`: the metric-isometry identity exhibits the
squared `L²` norm of the covariant gradient as the integrated
covariant-gradient term of the `H¹` inner product, which is bounded by the
squared `H¹` norm. -/
noncomputable def tensorCovGradL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r (s + 1) g :=
  (covGradL2Lin (I := I) (M := M) g r s).mkContinuous 1
    (fun w => covGradL2Lin_norm_le (I := I) (M := M) g r s w)

@[simp] lemma tensorCovGradL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2 (I := I) (M := M) g r s w =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := rfl

/-- The completion embedding `smoothToTensorH1Compl g r s` has dense range. -/
private lemma denseRange_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- The completion embedding `smoothToTensorH1Compl g r s` is
uniform-inducing. -/
private lemma isUniformInducing_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

/-- **The covariant gradient extended to the `H¹` completion.** The continuous
linear extension of `tensorCovGradL2 g r s` along the dense embedding
`smoothToTensorH1Compl` of smooth compactly-supported `H¹` sections into the
`H¹` Hausdorff completion `TensorH1Compl g r s`.

Since the codomain `TensorL2 r (s + 1) g` is a Hilbert space — hence complete
— the extension exists and is the unique continuous linear map from the `H¹`
completion to the one-rank-higher `L²` Hilbert space agreeing with the
bounded covariant gradient on smooth sections. -/
noncomputable def tensorCovGradL2Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorL2 r (s + 1) g :=
  ContinuousLinearMap.extend (tensorCovGradL2 (I := I) (M := M) g r s)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

/-- **Compatibility on smooth sections.** On the completion embedding of a
smooth compactly-supported `H¹` tensor section, the completion-extended
covariant gradient `tensorCovGradL2Compl g r s` recovers the bounded covariant
gradient `tensorCovGradL2 g r s`.

This is the defining property of the continuous linear extension along the
dense subspace of smooth sections. -/
theorem tensorCovGradL2Compl_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2Compl (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
      tensorCovGradL2 (I := I) (M := M) g r s w := by
  unfold tensorCovGradL2Compl
  exact ContinuousLinearMap.extend_eq
    (tensorCovGradL2 (I := I) (M := M) g r s)
    (e := smoothToTensorH1Compl (I := I) (M := M) g r s)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl (I := I) (M := M) g r s) w

/-- The completion-extended covariant gradient, evaluated on the completion
embedding of a smooth section, is the metric `L²`-coercion of the
section-level covariant gradient `covGrad g r s w.toCcTensor`. -/
theorem tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2Compl (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := by
  rw [tensorCovGradL2Compl_smoothToTensorH1Compl (I := I) (M := M) g r s w,
    tensorCovGradL2_apply]

set_option linter.unusedSectionVars false in
/-- **The operator-norm bound for the covariant-gradient operator.** The
bounded covariant-gradient operator `tensorCovGradL2 g r s` on smooth
compactly-supported `H¹` tensor sections has operator norm at most `1`. -/
theorem tensorCovGradL2_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ‖tensorCovGradL2 (I := I) (M := M) g r s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le (covGradL2Lin (I := I) (M := M) g r s)
    zero_le_one (fun w => covGradL2Lin_norm_le (I := I) (M := M) g r s w)

set_option linter.unusedSectionVars false in
/-- **The pointwise bound for the completion-extended covariant-gradient
operator.** For every element `x` of the `H¹` completion `TensorH1Compl g r s`,
the metric `L²` norm of `tensorCovGradL2Compl g r s x` is bounded by the `H¹`
norm of `x`.

The bound holds on the dense range of the completion embedding
`smoothToTensorH1Compl g r s` — there the extended operator recovers
`tensorCovGradL2 g r s`, and the metric `L²` norm of the covariant gradient is
bounded by the `H¹` norm by `covGrad_l2Norm_le_h1Norm` — and the inequality is
a closed condition, so it extends to the whole completion. -/
theorem tensorCovGradL2Compl_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : TensorH1Compl g r s) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s x‖ ≤ ‖x‖ := by
  have h_closed :
      IsClosed {y : TensorH1Compl g r s |
        ‖tensorCovGradL2Compl (I := I) (M := M) g r s y‖ ≤ ‖y‖} :=
    isClosed_le
      ((tensorCovGradL2Compl (I := I) (M := M) g r s).continuous.norm)
      continuous_norm
  have h_dense :
      ∀ w : SmoothCcTensorH1 g r s,
        ‖tensorCovGradL2Compl (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s w)‖ ≤
          ‖smoothToTensorH1Compl (I := I) (M := M) g r s w‖ := by
    intro w
    have h_rhs :
        ‖smoothToTensorH1Compl (I := I) (M := M) g r s w‖ = ‖w‖ := by
      rw [smoothToTensorH1Compl_apply, UniformSpace.Completion.norm_coe]
    have h_lhs :
        tensorCovGradL2Compl (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
          ((covGrad (I := I) (M := M) g r s w.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) :=
      tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe (I := I) (M := M)
        g r s w
    rw [h_lhs, h_rhs]
    exact covGrad_l2Norm_le_h1Norm (I := I) (M := M) g r s w
  exact (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s).induction_on
    x h_closed h_dense

set_option linter.unusedSectionVars false in
/-- **The operator-norm bound for the completion-extended covariant-gradient
operator.** The continuous linear extension `tensorCovGradL2Compl g r s` of the
covariant-gradient operator to the `H¹` completion `TensorH1Compl g r s` has
operator norm at most `1`.

This is `tensorCovGradL2Compl_apply_norm_le` repackaged through
`ContinuousLinearMap.opNorm_le_bound`. -/
theorem tensorCovGradL2Compl_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by
      rw [one_mul]
      exact tensorCovGradL2Compl_apply_norm_le (I := I) (M := M) g r s x)

set_option linter.unusedSectionVars false in
/-- **The smooth-case pairing formula for the covariant-gradient operator.**
For a smooth compactly-supported `H¹` tensor section `w` and a fixed smooth
compactly-supported `(r, s + 1)`-tensor section `T`, the metric `L²` inner
product of `tensorCovGradL2 g r s w` with the `L²`-coercion of `T` equals the
integral, against the Riemannian volume measure, of the pointwise
`(r, s + 1)`-tensor inner product of the section-level covariant gradient
`covGrad g r s w.toCcTensor` with `T`. -/
theorem tensorCovGradL2_inner_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) (T : SmoothCcTensor g r (s + 1)) :
    ⟪tensorCovGradL2 (I := I) (M := M) g r s w, (T : TensorL2 r (s + 1) g)⟫_ℝ =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s w.toCcTensor).toFun x)
          (T.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorCovGradL2_apply]
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def
      (covGrad (I := I) (M := M) g r s w.toCcTensor) T]
  rfl

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example : SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r (s + 1) g :=
  tensorCovGradL2 (I := I) (M := M) g r s

example : TensorH1Compl g r s →L[ℝ] TensorL2 r (s + 1) g :=
  tensorCovGradL2Compl (I := I) (M := M) g r s

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
