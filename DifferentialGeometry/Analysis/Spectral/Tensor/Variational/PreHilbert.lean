import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivSupport
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.Continuity
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Tensor.Multilinear.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn

/-!
# H^1 pre-Hilbert structure on compactly-supported smooth tensor sections

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file installs an `H^1` (gradient-augmented)
pre-Hilbert structure on a wrapper type around `SmoothCcTensor g r s`.

The `H^1` inner product `tensorH1Inner` (defined in `CovDerivPointwise`) is
the sum of the `L^2` inner product of the sections and the `L^2` inner
product of their covariant derivatives. Its algebraic properties — symmetry,
additivity, homogeneity, and diagonal non-negativity — combine the pointwise
algebra (from `CovDerivPointwise`) with integrability of the gradient
integrand (from `Continuity`).

## Main constructions

* `tensorH1Inner_symm`, `tensorH1Inner_nonneg`, `tensorH1Inner_add_left`,
  `tensorH1Inner_smul_left` — the global `H^1` inner-product algebra.
* `SmoothCcTensorH1 g r s` — a wrapper around `SmoothCcTensor g r s` carrying
  the `H^1` pre-Hilbert structure.
* `instPreInnerProductSpaceCore`, `instSeminormedAddCommGroup`,
  `instInnerProductSpace` — the pre-Hilbert / inner-product-space instances.
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
open DifferentialGeometry.Integral.DivergenceTheorem
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

/-- Symmetry of `tensorH1Inner`. -/
theorem tensorH1Inner_symm (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorH1Inner (I := I) (M := M) g r s T S := by
  unfold tensorH1Inner
  congr 1
  · exact tensorL2Inner_symm (I := I) (M := M) g r s S.toFun T.toFun
  · refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x

/-- Non-negativity of `tensorH1Inner` on the diagonal. -/
theorem tensorH1Inner_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    0 ≤ tensorH1Inner (I := I) (M := M) g r s S S := by
  unfold tensorH1Inner
  refine add_nonneg ?_ ?_
  · exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  · refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S x

/-- Additivity of `tensorH1Inner` in the first argument. -/
theorem tensorH1Inner_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorH1Inner (I := I) (M := M) g r s S₁ T +
        tensorH1Inner (I := I) (M := M) g r s S₂ T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
        tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
          tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (S₁ + S₂) T x) =
      (fun x : M => tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_add_left
      (I := I) (M := M) g r s S₁ S₂ T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_add
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₁ T)
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₂ T)]
  ring

/-- Homogeneity of `tensorH1Inner` in the first argument. -/
theorem tensorH1Inner_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorH1Inner (I := I) (M := M) g r s S T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
        c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (c • S) T x) =
      (fun x : M => c * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_smul_left
      (I := I) (M := M) g r s c S T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- Compactly-supported smooth `(r, s)`-tensor section wrapped to carry the
`H^1` pre-Hilbert structure, a distinct Lean type from `SmoothCcTensor`. -/
structure SmoothCcTensorH1 (g : SmoothRiemannianMetric I M) (r s : ℕ) where

  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorH1

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

/-- Two `SmoothCcTensorH1` are equal iff their underlying sections are equal. -/
@[ext] theorem ext {S T : SmoothCcTensorH1 g r s}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

/-- `toCcTensor` is injective. -/
lemma toCcTensor_injective :
    Function.Injective (fun S : SmoothCcTensorH1 g r s => S.toCcTensor) := by
  intro S T h
  exact ext h

instance : Zero (SmoothCcTensorH1 g r s) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorH1 g r s) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorH1 g r s) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorH1 g r s).toCcTensor = 0 := rfl
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorH1 g r s) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorH1 g r s) :
    (-S).toCcTensor = -S.toCcTensor := rfl
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorH1 g r s) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorH1 g r s) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

instance : SMul ℕ (SmoothCcTensorH1 g r s) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorH1 g r s) := ⟨zsmulRec⟩

@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorH1 g r s) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorH1 g r s) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

/-- Additive monoid hom from `SmoothCcTensorH1 g r s` to the underlying
compactly-supported smooth section. -/
def toCcTensorAddHom : SmoothCcTensorH1 g r s →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorH1

set_option linter.unusedSectionVars false in
/-- The pre-inner-product core on `SmoothCcTensorH1 g r s`, whose inner product
is the `H^1` pairing `tensorH1Inner g r s` of the underlying smooth
compactly-supported sections. -/
noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorH1 g r s) where
  inner S T := tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
  conj_inner_symm S T := by
    change (tensorH1Inner (I := I) (M := M) g r s T.toCcTensor S.toCcTensor : ℝ) =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    exact tensorH1Inner_symm (I := I) (M := M) g r s T.toCcTensor S.toCcTensor
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
    exact tensorH1Inner_nonneg (I := I) (M := M) g r s S.toCcTensor
  add_left S₁ S₂ T := by
    change tensorH1Inner (I := I) (M := M) g r s
        (S₁ + S₂).toCcTensor T.toCcTensor =
      tensorH1Inner (I := I) (M := M) g r s S₁.toCcTensor T.toCcTensor +
        tensorH1Inner (I := I) (M := M) g r s S₂.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact tensorH1Inner_add_left (I := I) (M := M) g r s
      S₁.toCcTensor S₂.toCcTensor T.toCcTensor
  smul_left S T c := by
    change tensorH1Inner (I := I) (M := M) g r s
        (c • S).toCcTensor T.toCcTensor =
      c * tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact tensorH1Inner_smul_left (I := I) (M := M) g r s
      c S.toCcTensor T.toCcTensor

set_option linter.unusedSectionVars false in
/-- The seminormed structure on `SmoothCcTensorH1 g r s` derived from the
pre-inner-product core. -/
noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

set_option linter.unusedSectionVars false in
/-- The inner-product-space structure on `SmoothCcTensorH1 g r s` derived from
the pre-inner-product core. -/
noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.ofCore _

set_option linter.unusedSectionVars false in
/-- The `H^1` inner product on `SmoothCcTensorH1 g r s` unfolds to the
`tensorH1Inner` pairing of the underlying smooth compactly-supported
sections. -/
@[simp] theorem SmoothCcTensorH1.inner_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensorH1 g r s) :
    ⟪S, T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := rfl

set_option linter.unusedSectionVars false in
/-- The `H^1` seminorm on `SmoothCcTensorH1 g r s` is the square root of the
`tensorH1Inner` pairing of the underlying section with itself. -/
theorem SmoothCcTensorH1.norm_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ = Real.sqrt (tensorH1Inner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) := rfl

section InstanceTests

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) := inferInstance

end InstanceTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
