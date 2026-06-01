import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Integral.L2.Hilbert.Inherited
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# H¹ Hilbert completion of tensor sections and the H¹ → L² bounded inclusion

For a closed Riemannian manifold `(M, g)`, the seminormed inner-product space
`SmoothCcTensorH1 g r s` of compactly-supported smooth `(r, s)`-tensor
sections (equipped with the H¹ inner product `tensorH1Inner`) has Hausdorff
completion `TensorH1Compl g r s`. By Mathlib's automatic instances on
completions of (semi-)inner-product spaces, `TensorH1Compl g r s` is a real
Hilbert space.

The natural inclusion of smooth compactly-supported tensor sections (with H¹
norm) into the tensor L² Hilbert space `TensorL2 r s g` is non-expansive,
since the H¹ inner product equals the L² inner product plus the integral of
the non-negative pointwise covariant-derivative inner product. By the
universal property of the uniform completion this extends to a continuous
linear map `TensorH1Compl g r s →L[ℝ] TensorL2 r s g`.
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

/-- The tensor H¹ Hilbert space of `(M, g)` defined as the Hausdorff
completion of the pre-Hilbert space `SmoothCcTensorH1 g r s` of smooth
compactly-supported `(r, s)`-tensor sections equipped with the H¹ inner
product.

By the standard theory of completions of inner-product spaces,
`TensorH1Compl g r s` inherits `NormedAddCommGroup`, `NormedSpace ℝ`,
`InnerProductSpace ℝ`, and `CompleteSpace`, making it a real Hilbert
space. -/
abbrev TensorH1Compl (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  UniformSpace.Completion (SmoothCcTensorH1 g r s)

/-- The canonical embedding `SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s`
of smooth compactly-supported tensor sections (with H¹ inner product) into
the H¹ completion as a continuous linear map. -/
noncomputable def smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToTensorH1Compl_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothToTensorH1Compl (I := I) (M := M) g r s S =
      (S : TensorH1Compl g r s) :=
  rfl

set_option linter.unusedSectionVars false in
/-- The squared seminorm of a smooth compactly-supported tensor section in
the L² pre-Hilbert space equals the L² self-pairing. -/
lemma SmoothCcTensor.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    ‖S‖ ^ 2 = tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
  have h := real_inner_self_eq_norm_sq S
  rw [SmoothCcTensor.inner_def] at h
  exact h.symm

set_option linter.unusedSectionVars false in
/-- The squared seminorm of a smooth compactly-supported tensor section in
the H¹ pre-Hilbert space equals the H¹ self-pairing. -/
lemma SmoothCcTensorH1.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ ^ 2 =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor := by
  have h := real_inner_self_eq_norm_sq S
  rw [SmoothCcTensorH1.inner_def] at h
  exact h.symm

set_option linter.unusedSectionVars false in
/-- The squared L² seminorm of a smooth compactly-supported tensor section
is bounded above by its squared H¹ seminorm. -/
lemma SmoothCcTensorH1.l2NormSq_le_h1NormSq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) S.toCcTensor,
    SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S,
    tensorH1Inner_def]
  have h_grad_nonneg :
      0 ≤ ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
              S.toCcTensor S.toCcTensor x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s
      S.toCcTensor x
  linarith

set_option linter.unusedSectionVars false in
/-- The L² seminorm of a smooth compactly-supported tensor section is
bounded above by its H¹ seminorm. -/
lemma SmoothCcTensorH1.l2Norm_le_h1Norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ≤ ‖S‖ := by
  have h_sq := SmoothCcTensorH1.l2NormSq_le_h1NormSq (I := I) (M := M) S
  have h_rhs_nn : 0 ≤ ‖S‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

set_option linter.unusedSectionVars false in
/-- The bound stated in the `mkContinuous` form: `‖S.toCcTensor‖ ≤ 1 * ‖S‖`. -/
lemma SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]; exact SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S

/-- The linear map from H¹ pre-Hilbert smooth compactly-supported tensor
sections to the L² Hilbert space, sending each smooth section to its image
under the canonical L² embedding `SmoothCcTensor g r s → TensorL2 r s g`. -/
noncomputable def smoothCcTensorH1ToTensorL2Lin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] TensorL2 r s g where
  toFun S := (S.toCcTensor : TensorL2 r s g)
  map_add' S T := by
    change ((S + T).toCcTensor : TensorL2 r s g) =
      (S.toCcTensor : TensorL2 r s g) + (T.toCcTensor : TensorL2 r s g)
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c S := by
    change ((c • S).toCcTensor : TensorL2 r s g) =
      c • (S.toCcTensor : TensorL2 r s g)
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact UniformSpace.Completion.coe_smul _ _

@[simp] lemma smoothCcTensorH1ToTensorL2Lin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S =
      (S.toCcTensor : TensorL2 r s g) := rfl

set_option linter.unusedSectionVars false in
/-- Norm bound for the underlying linear map: the L² norm of the image of
`S` is bounded by the H¹ norm of `S`. -/
lemma smoothCcTensorH1ToTensorL2Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S‖ ≤ 1 * ‖S‖ := by
  have h_coe_norm :
      ‖(S.toCcTensor : TensorL2 r s g)‖ = ‖S.toCcTensor‖ :=
    UniformSpace.Completion.norm_coe _
  calc ‖smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S‖
      = ‖(S.toCcTensor : TensorL2 r s g)‖ := rfl
    _ = ‖S.toCcTensor‖ := h_coe_norm
    _ ≤ 1 * ‖S‖ :=
      SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm (I := I) (M := M) S

/-- The continuous linear map from H¹ pre-Hilbert smooth compactly-supported
tensor sections into the tensor L² Hilbert space, with operator norm
bounded by `1`. -/
noncomputable def smoothCcTensorH1ToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r s g :=
  (smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s).mkContinuous 1
    (fun S => smoothCcTensorH1ToTensorL2Lin_norm_le (I := I) (M := M) g r s S)

@[simp] lemma smoothCcTensorH1ToTensorL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s S =
      (S.toCcTensor : TensorL2 r s g) := rfl

/-- `UniformSpace.Completion.toComplL` from `SmoothCcTensorH1 g r s` to
`TensorH1Compl g r s` has dense range. -/
private lemma denseRange_toComplL_smoothCcTensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange
      (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s) := by
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- `UniformSpace.Completion.toComplL` from `SmoothCcTensorH1 g r s` to
`TensorH1Compl g r s` is uniform-inducing. -/
private lemma isUniformInducing_toComplL_smoothCcTensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s) := by
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

/-- The continuous linear extension of `smoothCcTensorH1ToTensorL2` along the
dense embedding `smoothToTensorH1Compl`. Since `TensorL2 r s g` is complete
(a Hilbert space), the extension exists and is the unique continuous linear
map from the H¹ completion to the L² Hilbert space agreeing with the L²
embedding on smooth sections. -/
noncomputable def TensorH1ComplToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorL2 r s g :=
  ContinuousLinearMap.extend (smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s)
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s)

@[simp] lemma TensorH1ComplToTensorL2_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s S := by
  unfold TensorH1ComplToTensorL2
  exact ContinuousLinearMap.extend_eq
    (smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothCcTensorH1 (I := I) (M := M) g r s)
    (isUniformInducing_toComplL_smoothCcTensorH1 (I := I) (M := M) g r s) S

/-- Compatibility: on smooth compactly-supported sections, the H¹-to-L² map
agrees with the L² embedding of the underlying section. -/
theorem TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      (S.toCcTensor : TensorL2 r s g) := by
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl,
    smoothCcTensorH1ToTensorL2_apply]

section InstanceTests

example (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ := TensorH1Compl g r s

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    NormedAddCommGroup (TensorH1Compl g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (TensorH1Compl g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CompleteSpace (TensorH1Compl g r s) := inferInstance

end InstanceTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
