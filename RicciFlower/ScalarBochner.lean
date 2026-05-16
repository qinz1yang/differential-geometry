import RicciFlower.Operators.HessianTrace
import RicciFlower.RoughLaplacian
import RicciFlower.Curvature.Components
import RicciFlower.Tensor.RicciIdentity
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.RSTensor.NablaOnTensors
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Scalar Bochner Formula

This file contains the RicciFlower-facing scalar Bochner endpoint.  The fully
geometric work is split into named realized frontier hypotheses:

* the one-form norm product rule;
* the Weitzenbock/commutator identity for `du`.

The endpoint theorem below composes those two facts with the concrete realized
gradient/cotangent bridges.  No synthetic imports are used.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Squared norm of the realized gradient of a scalar function. -/
def gradNormSq (g : SmoothRiemannianMetric I M) (u : M -> Real) : M -> Real :=
  fun x => g.inner x (gradientFun (I := I) g u x) (gradientFun (I := I) g u x)

/-- Squared norm of a supplied Hessian two-tensor. -/
def hessianNormSq
    (g : SmoothRiemannianMetric I M)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    M -> Real :=
  fun x => normSq0S (I := I) g x 2 (Hess x)

/-- The Ricci term in the scalar Bochner formula. -/
def ricciGradGrad
    (Ric : Tensor02Section (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (u : M -> Real) : M -> Real :=
  fun x => Ric x (vec2 (gradientFun (I := I) g u x) (gradientFun (I := I) g u x))

/-- Raising `du` by the metric recovers the realized gradient. -/
theorem cotangentSharp_differential1FormFun_eq_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    cotangentSharp (I := I) g x (differential1FormFun (I := I) u x) =
      gradientFun (I := I) g u x := by
  apply (metricFlatEquiv (I := I) g x).injective
  ext X
  change
    g.inner x (cotangentSharp (I := I) g x (differential1FormFun (I := I) u x)) X =
      g.inner x (gradientFun (I := I) g u x) X
  rw [cotangentSharp_inner, inner_gradientFun]
  rfl

/-- Inner product of `du` with `dv` is the metric inner product of gradients. -/
theorem inner0S_differential1FormFun_pair_eq_grad_inner
    (g : SmoothRiemannianMetric I M) (u v : M -> Real) (x : M) :
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) u x)
        (differential1FormFun (I := I) v x) =
      g.inner x (gradientFun (I := I) g u x) (gradientFun (I := I) g v x) := by
  rw [Tensor0SBundle.inner0S_one_eq_cotangent, cotangentInner_eq_sharp]
  rw [cotangentSharp_differential1FormFun_eq_gradientFun,
    cotangentSharp_differential1FormFun_eq_gradientFun]

/-- Pairing one-forms with the metric equals evaluating the first one-form on
the sharp of the second. -/
theorem inner0S_one_eq_eval_sharp_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    inner0S (I := I) g x 1 α β =
      cotangentToDual (I := I) α (cotangentSharp (I := I) g x β) := by
  rw [Tensor0SBundle.inner0S_one_eq_cotangent, cotangentInner_eq_sharp,
    cotangentSharp_inner]

/-- The norm of `du` agrees with the squared norm of `grad u`. -/
theorem inner0S_differential1FormFun_eq_gradNormSq
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) u x)
        (differential1FormFun (I := I) u x) =
      gradNormSq (I := I) g u x := by
  rw [inner0S_differential1FormFun_pair_eq_grad_inner]
  rfl

/-! ## Named Bochner frontier hypotheses -/

/-- The one-form norm product rule at a point.

Mathematically this is
`1/2 Δ |α|² = <roughΔ α, α> + |∇α|²`.  The rough Laplacian one-form and
the covariant-derivative two-tensor are supplied explicitly until the tensor
rough-Laplacian API is bundled. -/
def OneFormNormBochnerAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (α roughAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  (1 / 2 : Real) *
      laplacian (I := I) cov g
        (fun y : M => inner0S (I := I) g y 1 (α y) (α y)) x =
    inner0S (I := I) g x 1 (roughAlpha x) (α x) +
      normSq0S (I := I) g x 2 (nablaAlpha x)

/-- The commutator/Weitzenbock identity for the differential one-form `du`,
paired with `du`.

Mathematically this packages
`roughΔ(du) = d(Δu) + Ric(du)` after pairing with `du`. -/
def DifferentialOneFormCommutatorAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M) : Prop :=
  inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
        (differential1FormFun (I := I) u x) +
      ricciGradGrad (I := I) Ric g u x

/-- Primary pointwise one-form commutator interface:
`roughDu = d(Δu) + Ric(·, ∇u)` at `x`. -/
def OneFormCommutatorEvalAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M) : Prop :=
  ∀ Y : TangentSpace I x,
    roughDu x (fun _ : Fin 1 => Y) =
      differential1FormFun (I := I) (laplacian (I := I) cov g u) x
          (fun _ : Fin 1 => Y) +
        Ric x (vec2 Y (gradientFun (I := I) g u x))

/-- Intrinsic traced Hessian-derivative term that should realize
`d (Delta u)`. -/
def traceNablaHessianForDLap
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  metricTraceLastTwo0SAt3 (I := I) g nabla2Du Y

/-- Basis-coordinate version of `traceNablaHessianForDLap`. -/
def traceNablaHessianForDLapInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  traceNablaOneFormAt (I := I) basis gInv nabla2Du Y

/-- Pointwise producer saying that the traced Hessian derivative is `d(Delta u)`. -/
def TraceNablaHessianRealizesDLapAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (u : M -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    traceNablaHessianForDLap (I := I) g nabla2Du Y =
      differential1FormFun (I := I) (laplacian (I := I) cov g u) x
        (fun _ : Fin 1 => Y)

/-- Basis-coordinate compatibility version of
`TraceNablaHessianRealizesDLapAt`. -/
def TraceNablaHessianRealizesDLapAtInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (u : M -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    traceNablaHessianForDLapInBasis (I := I) basis gInv nabla2Du Y =
      differential1FormFun (I := I) (laplacian (I := I) cov g u) x
        (fun _ : Fin 1 => Y)

/-- A basis-coordinate `d(Delta u)` trace realization follows from the
intrinsic one. -/
theorem TraceNablaHessianRealizesDLapAt.toInBasis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (u : M -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du) :
    TraceNablaHessianRealizesDLapAtInBasis (I := I) cov g basis gInv u nabla2Du := by
  intro Y
  unfold traceNablaHessianForDLapInBasis traceNablaOneFormAt
  rw [← h Y]
  unfold traceNablaHessianForDLap
  exact (metricTraceLastTwo0SAt3_eq_sum_basis (I := I) g basis gInv hinv
    nabla2Du Y).symm

/-- Pointwise producer for the Ricci commutator trace term:
`tr_g ∇²du(.,.,Y) = tr_g ∇²du(Y,.,.) + Ric(Y, grad u)`. -/
def OneFormRicciTraceCommAt
    {Idx : Type*} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv
    (gradientFun (I := I) g u x) nabla2Du

/-- Coordinate-frame specialization of the one-form Ricci trace commutator at
one point. The basis is the chart-induced tangent basis from
`Coordinates.coordinateFrameAt_toBasis`; the bracket-free coordinate fact is
kept in the coordinate-frame layer. -/
def oneFormRicciTraceComm_coordAt
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (x₀ : M)
    (gInv : Coordinates.CoordinateIdx (𝕜 := Real) E -> Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    Prop :=
  OneFormRicciTraceCommAt (I := I) g Ric u
    (Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv nabla2Du

theorem oneFormRicciTraceComm_coordAt_iff
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (x₀ : M)
    (gInv : Coordinates.CoordinateIdx (𝕜 := Real) E -> Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    oneFormRicciTraceComm_coordAt (I := I) g Ric u x₀ gInv nabla2Du ↔
      OneFormRicciTraceCommAt (I := I) g Ric u
        (Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv nabla2Du :=
  Iff.rfl

/-- The signed curvature trace appearing when commuting the first two slots of
`∇²du`.

The leading minus sign matches the realized convention
`Rm13 alpha X Y Z = alpha (R(X,Y)Z)`, since covectors see the negative
curvature action. -/
def curvatureTraceDuAt
    {Idx : Type*} [Fintype Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Y : TangentSpace I x) : Real :=
  curvatureTraceOneFormAt (I := I) Rm13
    (differential1FormFun (I := I) u x) basis gInv Y

/-- The metric trace of the one-form curvature commutator realizes
`Ric(Y, ∇u)`. -/
def CurvatureTraceDuEqRicciGradAt
    {Idx : Type*} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) : Prop :=
  CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13
    (differential1FormFun (I := I) u x) basis gInv
    (gradientFun (I := I) g u x)

/-- The pointwise differential one-form is the metric dual of the gradient. -/
theorem differential1FormFun_eq_metric_dual_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    differential1FormFun (I := I) u x =
      dualToCotangent (I := I)
        ((tangentFlatLinear (I := I) g x) (gradientFun (I := I) g u x)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  ext V
  simp only [cotangentToDualLinear_apply, cotangentToDual_apply, gradientFun_eq, metricSharp_eq,
    cotangentToDual_dualToCotangent, tangentFlatLinear_apply]
  exact (inner_gradientFun (I := I) g u x V).symm

/-- The curvature trace term for `du` is the Ricci-gradient pairing, assuming
the `(1,3)` curvature tensor is the Ricci trace source and satisfies the
metric skew-adjointness of the curvature endomorphism. -/
theorem curvatureTraceDuEqRicciGradAt_of_metric_dual
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    CurvatureTraceDuEqRicciGradAt (I := I) g Ric Rm13 u basis gInv := by
  exact curvatureTraceOneFormEqRicVectorAt_of_metric_dual (I := I) g Ric Rm13
    (differential1FormFun (I := I) u x) basis gInv
    (gradientFun (I := I) g u x) hinv hRic hSkew
    (differential1FormFun_eq_metric_dual_gradientFun (I := I) g u x)

/-- Coordinate components of the supplied second covariant derivative of `du`
in a pointwise tangent basis. -/
def nabla2DuCoord
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (i j k : Idx) : Real :=
  nabla2OneFormCoord (I := I) basis nabla2Du i j k

/-- Signed curvature-action components for `du`.  The minus sign is the
covector curvature-action sign for the convention
`Rm13 alpha X Y Z = alpha (R(X,Y)Z)`. -/
def curvatureActionOnDuCoord
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (i k j : Idx) : Real :=
  curvatureActionOnOneFormCoord (I := I) Rm13
    (differential1FormFun (I := I) u x) basis i k j

/-- Ricci-gradient components in a pointwise tangent basis. -/
def ricGradCoord
    {Idx : Type*}
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (k : Idx) : Real :=
  ricciVectorCoord (I := I) Ric basis (gradientFun (I := I) g u x) k

theorem nabla2DuTrailingSymmCoord_of_tensor
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du) :
    Nabla2DuTrailingSymmCoord (nabla2DuCoord (I := I) basis nabla2Du) := by
  simpa [nabla2DuCoord] using
    nabla2OneFormTrailingSymmCoord_of_tensor (I := I) basis nabla2Du hsymm

theorem curvatureActionTraceEqualsRicGradCoord_of_tensor
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hcurv : CurvatureTraceDuEqRicciGradAt (I := I) g Ric Rm13 u basis gInv) :
    CurvatureActionTraceEqualsRicGradCoord gInv
      (curvatureActionOnDuCoord (I := I) Rm13 u basis)
      (ricGradCoord (I := I) g Ric u basis) := by
  simpa [curvatureActionOnDuCoord, ricGradCoord, CurvatureTraceDuEqRicciGradAt] using
    curvatureActionTraceEqualsRicVectorCoord_of_tensor (I := I) Ric Rm13
      (differential1FormFun (I := I) u x) basis gInv
      (gradientFun (I := I) g u x) hcurv

/-- Coordinate-frame producer for the existing trace commutator interface.

The coordinate-frame theorem supplies the bracket-free frame package; the
remaining geometric inputs are still the one-form Ricci identity, trailing-slot
symmetry, and curvature trace-to-Ricci identification. -/
theorem oneFormRicciTraceComm_coordAt_of_third_comm
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (x₀ : M)
    (gInv : Coordinates.CoordinateIdx (𝕜 := Real) E -> Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x₀) nabla2Du)
    (hcurv : CurvatureTraceDuEqRicciGradAt (I := I) g Ric Rm13 u
      (Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv) :
    oneFormRicciTraceComm_coordAt (I := I) g Ric u x₀ gInv nabla2Du := by
  rw [oneFormRicciTraceComm_coordAt_iff]
  simpa [OneFormRicciTraceCommAt, CurvatureTraceDuEqRicciGradAt, curvatureTraceDuAt] using
    oneForm_ricci_trace_comm_of_third_comm (I := I) Ric Rm13
      (differential1FormFun (I := I) u x₀)
      (Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv
      (gradientFun (I := I) g u x₀) nabla2Du hsymm hcomm
      (by
        intro Y
        simpa [CurvatureTraceDuEqRicciGradAt, curvatureTraceDuAt,
          curvatureTraceOneFormAt] using hcurv Y)

/-- Pairing the pointwise commutator with `du` gives the scalar commutator
term used by Bochner. -/
theorem oneForm_commutator_pair_of_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x := by
  unfold DifferentialOneFormCommutatorAt
  rw [inner0S_one_eq_eval_sharp_right (I := I) g x
    (roughDu x) (differential1FormFun (I := I) u x)]
  rw [inner0S_one_eq_eval_sharp_right (I := I) g x
    (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
    (differential1FormFun (I := I) u x)]
  rw [cotangentSharp_differential1FormFun_eq_gradientFun]
  simpa [OneFormCommutatorEvalAt, ricciGradGrad, cotangentToDual_apply] using
    hcomm (gradientFun (I := I) g u x)

/-- The covariant derivative of `du` realizes the Hessian norm used in the
scalar Bochner formula. -/
def HessianNormRealizesNablaDifferentialAt
    (g : SmoothRiemannianMetric I M)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  normSq0S (I := I) g x 2 (nablaDu x) =
    hessianNormSq (I := I) g Hess x

/-- Coordinate expression for `<tr_g ∇²α, α>`. -/
def oneFormRoughInnerCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (αx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
      αx (fun _ : Fin 1 => basis j)

/-- Coordinate expression for `|∇α|²`. -/
def oneFormNablaNormCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    gInv i k * gInv j l *
      nablaAlphaX (vec2 (basis i) (basis j)) *
        nablaAlphaX (vec2 (basis k) (basis l))

/-- Component-level product rule for the second derivative of the pointwise
one-form norm in a basis, already weighted by the trace coefficient. This
avoids dividing by inverse-metric components, which may be zero. -/
def OneFormNormSecondProductInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  ∀ i j : Idx,
    gInv i j *
        normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
      (2 : Real) *
        (gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
            alphaX (fun _ : Fin 1 => basis j) +
          ∑ k : Idx, ∑ l : Idx,
            gInv i k * gInv j l *
              nablaAlphaX (vec2 (basis i) (basis j)) *
                nablaAlphaX (vec2 (basis k) (basis l)))

/-- Metric-trace product rule for the scalar norm of a one-form.

This is the honest analytic producer for the coordinate calculation: it says
that the trace of the supplied scalar second derivative of `|alpha|^2` is the
sum of the rough-inner and `|nabla alpha|^2` coordinate terms. -/
def MetricTraceInnerProductRuleAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
    (2 : Real) *
      (oneFormRoughInnerCoord (I := I) basis gInv alphaX nabla2Alpha +
        oneFormNablaNormCoord (I := I) basis gInv nablaAlphaX)

theorem metricTrace_inner_product_rule
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : MetricTraceInnerProductRuleAt (I := I) basis gInv alphaX nablaAlphaX
      nabla2Alpha normSecond) :
    metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
      (2 : Real) *
        (oneFormRoughInnerCoord (I := I) basis gInv alphaX nabla2Alpha +
          oneFormNablaNormCoord (I := I) basis gInv nablaAlphaX) :=
  h

/-- The component product rule implies the traced product rule used by the
one-form Bochner norm identity. -/
theorem metricTrace_inner_product_rule_of_second_product
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hprod : OneFormNormSecondProductInBasis (I := I) basis gInv alphaX
      nablaAlphaX nabla2Alpha normSecond) :
    MetricTraceInnerProductRuleAt (I := I) basis gInv alphaX nablaAlphaX
      nabla2Alpha normSecond := by
  classical
  unfold MetricTraceInnerProductRuleAt metricTrace0S2InBasis
    oneFormRoughInnerCoord oneFormNablaNormCoord
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))
        =
      ∑ i : Idx, ∑ j : Idx,
        (2 : Real) *
          (gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
              alphaX (fun _ : Fin 1 => basis j) +
            ∑ k : Idx, ∑ l : Idx,
              gInv i k * gInv j l *
                nablaAlphaX (vec2 (basis i) (basis j)) *
                  nablaAlphaX (vec2 (basis k) (basis l))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hprod i j
    _ =
      (2 : Real) *
        ((∑ i : Idx, ∑ j : Idx,
            gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
              alphaX (fun _ : Fin 1 => basis j)) +
          ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * gInv j l *
                nablaAlphaX (vec2 (basis i) (basis j)) *
                nablaAlphaX (vec2 (basis k) (basis l))) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          simp_rw [Finset.mul_sum]

/-- Explicit coordinate product-rule input for the one-form Bochner norm
identity. This is the analytic normal-frame calculation, separated from the
finite-sum consumer theorem below. -/
def OneFormNormProductRuleInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (α : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) : Prop :=
  (1 / 2 : Real) *
      laplacian (I := I) cov g
        (fun y : M => inner0S (I := I) g y 1 (α y) (α y)) x =
    oneFormRoughInnerCoord (I := I) basis gInv (α x) nabla2Alpha +
      oneFormNablaNormCoord (I := I) basis gInv (nablaAlpha x)

/-- Pairing a rough one-form with `α` is the coordinate rough-inner sum once
the rough one-form realizes the metric trace of the second covariant derivative. -/
theorem rough_inner_eq_coord_of_trace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (αx roughAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) roughAlphaX nabla2Alpha) :
    inner0S (I := I) g x 1 roughAlphaX αx =
      oneFormRoughInnerCoord (I := I) basis gInv αx nabla2Alpha := by
  rw [inner0S_one_eq_cotangent,
    cotangentInner_eq_coord (I := I) g x basis gInv hinv]
  unfold oneFormRoughInnerCoord
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hrough_i :
      (cotangentToDual (I := I) roughAlphaX) (basis i) =
        roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) := by
    simpa [cotangentToDual_apply] using
      roughLap1FormAt_eq_of_realizes (I := I) basis gInv roughAlphaX
        nabla2Alpha hrough (basis i)
  rw [hrough_i]
  simp [cotangentToDual_apply, mul_assoc]

/-- The norm of a covariant derivative two-tensor is the direct `(0,2)`
coordinate norm sum. -/
theorem nabla_norm_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    normSq0S (I := I) g x 2 nablaAlphaX =
      oneFormNablaNormCoord (I := I) basis gInv nablaAlphaX := by
  simpa [oneFormNablaNormCoord, vec2] using
    Tensor0SBundle.normSq0S_two_eq_coord (I := I) (M := M) g x
      basis gInv hinv nablaAlphaX

/-- The coordinate one-form norm product rule follows from the scalar
Laplacian trace realization and the explicit metric-trace product rule. -/
theorem oneForm_norm_product_rule_of_trace
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaRaw : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv
      (fun y : M => inner0S (I := I) g y 1 (alphaRaw y) (alphaRaw y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond) :
    OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      alphaRaw nablaAlpha nabla2Alpha := by
  unfold OneFormNormProductRuleInBasis ScalarLaplacianRealizesTraceAtInBasis at *
  rw [hlap, htrace]
  ring

/-- Compatibility wrapper for the coordinate one-form norm product rule.

The analytic content is the explicit trace product-rule input `htrace`; this
wrapper keeps the section-level arguments near the downstream Bochner assembly
without carrying a separate Levi-Civita predicate. -/
theorem oneForm_norm_product_rule_of_metric_compatible
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (_alpha : OneFormSection (I := I) (M := M))
    (alphaRaw : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (_nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv
      (fun y : M => inner0S (I := I) g y 1 (alphaRaw y) (alphaRaw y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond) :
    OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      alphaRaw nablaAlpha nabla2Alpha :=
  oneForm_norm_product_rule_of_trace (I := I) cov g basis gInv
    alphaRaw nablaAlpha nabla2Alpha normSecond hlap htrace

/-- Compatibility wrapper from the weighted component product rule to the
traced product rule. -/
theorem oneForm_norm_second_product_of_metric_compatible
    {Idx : Type*} [Fintype Idx]
    (_cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (_alpha : OneFormSection (I := I) (M := M))
    (alphaRaw : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (_nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hprod : OneFormNormSecondProductInBasis (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond) :
    MetricTraceInnerProductRuleAt (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond :=
  metricTrace_inner_product_rule_of_second_product (I := I) basis gInv
    (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond hprod

/-- Coordinate consumer for the one-form norm product rule.

The analytic content is exactly `hprod`; this theorem only rewrites the two
coordinate sums back to the intrinsic rough-inner and `(0,2)` norm terms. -/
theorem oneForm_norm_bochner_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α roughAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (hprod : OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      α nablaAlpha nabla2Alpha)
    (_hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) (roughAlpha x) nabla2Alpha) :
    OneFormNormBochnerAt (I := I) cov g α roughAlpha nablaAlpha x := by
  unfold OneFormNormBochnerAt
  rw [hprod]
  rw [rough_inner_eq_coord_of_trace (I := I) g basis gInv hinv
    (α x) (roughAlpha x) nabla2Alpha _hrough]
  rw [nabla_norm_eq_coord (I := I) g basis gInv hinv (nablaAlpha x)]

/-- One-form norm Bochner producer, isolated through the coordinate frontier. -/
theorem oneForm_norm_bochner_at
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α roughAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (hprod : OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      α nablaAlpha nabla2Alpha)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) (roughAlpha x) nabla2Alpha) :
    OneFormNormBochnerAt (I := I) cov g α roughAlpha nablaAlpha x :=
  oneForm_norm_bochner_coord (I := I) cov g basis gInv hinv
    α roughAlpha nablaAlpha nabla2Alpha hprod hrough

/-- If a supplied Hessian tensor agrees pointwise with the covariant derivative
of `du`, then its norm is the Hessian norm used in scalar Bochner. -/
theorem hessian_realizes_nabla_du
    (g : SmoothRiemannianMetric I M)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) (h : nablaDu x = Hess x) :
    HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x := by
  unfold HessianNormRealizesNablaDifferentialAt hessianNormSq
  rw [h]

/-- Component equality in a basis is enough to identify the supplied Hessian
with `nablaDu`, hence to realize the Hessian norm. -/
theorem hessian_norm_realizes_of_nabla_du
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hcomp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x :=
  hessian_realizes_nabla_du (I := I) g Hess nablaDu x
    (ext0S_basis (I := I) basis hcomp)

/-- Components of `nablaDu` agree with a supplied Hessian in a basis, provided
the basis vectors are realized by smooth vector fields at the point. -/
theorem hessian_components_of_nabla_du
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : OneFormSection (I := I) (M := M))
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (hnabla : NablaOneFormRealizesAt (I := I) cov du nablaDu x) :
    ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots := by
  intro slots
  let X0 := X (slots 0)
  let Y := basis (slots 1)
  have hvec : vec2 (X0 x) Y = fun a : Fin 2 => basis (slots a) := by
    funext a
    fin_cases a
    · simp [X0, Y, vec2, RicciFlower.Curvature.vec2, hfields (slots 0)]
    · simp [Y, vec2, RicciFlower.Curvature.vec2]
  have hn := hnabla X0 Y
  have hh := hHess X0 Y
  change nablaDu x (fun a : Fin 2 => basis (slots a)) =
    Hess x (fun a : Fin 2 => basis (slots a))
  rw [← hvec]
  rw [hn, hh]
  rfl

/-- Accessor form of the one-form commutator frontier for `du`. -/
theorem roughLap_du_eq_d_lap_add_ric_of_comm
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (hcomm : DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x) :
    inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
      inner0S (I := I) g x 1
          (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
          (differential1FormFun (I := I) u x) +
        ricciGradGrad (I := I) Ric g u x :=
  hcomm

/-- Component Ricci-identity frontier for one-forms.

This is the remaining geometric producer: it should prove the pointwise
commutator `roughDu = d(Δu) + Ric(·, ∇u)` from the tensor Ricci identity,
the rough-Laplacian trace realization, and curvature trace realization. -/
theorem oneForm_ricci_identity_components
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (_hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (_hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (_hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (_hdu : DuFieldRealizes (I := I) u duSec)
    (_hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du)
    (hcomm : OneFormRicciTraceCommAt (I := I) g Ric u basis gInv nabla2Du) :
    OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x := by
  have hroughBasis : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) (roughDu x) nabla2Du :=
    rough_lap_one_form_realizes_metric_trace (I := I) g basis gInv
      nabla2Du (roughDu x) hrough _hinv
  have hdlapBasis : TraceNablaHessianRealizesDLapAtInBasis (I := I)
      cov g basis gInv u nabla2Du :=
    TraceNablaHessianRealizesDLapAt.toInBasis (I := I) cov g basis gInv
      _hinv u nabla2Du hdlap
  intro Y
  calc
    roughDu x (fun _ : Fin 1 => Y)
        = roughLap1FormAt (I := I) basis gInv nabla2Du Y := by
          exact roughLap1FormAt_eq_of_realizes (I := I) basis gInv (roughDu x)
            nabla2Du hroughBasis Y
    _ = traceNablaHessianForDLapInBasis (I := I) basis gInv nabla2Du Y +
          Ric x (vec2 Y (gradientFun (I := I) g u x)) := by
          simpa [OneFormRicciTraceCommAt, traceNablaHessianForDLapInBasis] using
            (show OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv
              (gradientFun (I := I) g u x) nabla2Du from hcomm) Y
    _ = differential1FormFun (I := I) (laplacian (I := I) cov g u) x
            (fun _ : Fin 1 => Y) +
          Ric x (vec2 Y (gradientFun (I := I) g u x)) := by
          rw [hdlapBasis Y]

/-- Ricci trace commutator from the three geometric one-form inputs.

The strengthened `Nabla2OneFormRealizesAt` records that `nabla2Du` is the true
iterated derivative of `du`; the still-separate geometric producers are
trailing-slot symmetry, the untraced one-form curvature commutator, and the
metric skew-adjointness needed to trace curvature to Ricci. -/
theorem one_form_ricci_trace_comm_of_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (_hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (_hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (_hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (_hdu : DuFieldRealizes (I := I) u duSec)
    (_hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    OneFormRicciTraceCommAt (I := I) g Ric u basis gInv nabla2Du := by
  exact oneForm_ricci_trace_comm_of_third_comm (I := I) Ric Rm13
    (differential1FormFun (I := I) u x) basis gInv
    (gradientFun (I := I) g u x) nabla2Du hsymm hthird
    (by
      have hcurv := curvatureTraceDuEqRicciGradAt_of_metric_dual
        (I := I) g Ric Rm13 u basis gInv _hinv _hRic hSkew
      intro Y
      simpa [CurvatureTraceDuEqRicciGradAt, curvatureTraceDuAt,
        curvatureTraceOneFormAt] using hcurv Y)

/-- Geometric wrapper exposing the pointwise commutator interface from the
component Ricci-identity frontier. -/
theorem oneForm_commutator_eval_of_components
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du)
    (hcomm : OneFormRicciTraceCommAt (I := I) g Ric u basis gInv nabla2Du) :
    OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x :=
  oneForm_ricci_identity_components (I := I) cov g Ric Rm13 u roughDu
    basis gInv duSec nablaDu nablaDuSec nabla2Du
    hinv hRm hRic hdu hnabla hnabla2 hrough hdlap hcomm

/-- Geometric wrapper using the Ricci trace-commutator frontier to supply the
pointwise commutator interface. -/
theorem oneForm_commutator_eval_of_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du) :
    OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x :=
  oneForm_commutator_eval_of_components (I := I) cov g Ric Rm13 u roughDu
    basis gInv duSec nablaDu nablaDuSec nabla2Du
    hinv hRm hRic hdu hnabla hnabla2 hrough hdlap
    (one_form_ricci_trace_comm_of_lc (I := I) cov g Ric Rm13 u basis gInv
      duSec nablaDu nablaDuSec nabla2Du
      hinv hRm hRic hdu hnabla hnabla2 hsymm hthird hSkew)

/-- One-form commutator formula for `du`, produced from the primary pointwise
commutator interface. -/
theorem roughLap_du_eq_d_lap_add_ric
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
      inner0S (I := I) g x 1
          (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
          (differential1FormFun (I := I) u x) +
        ricciGradGrad (I := I) Ric g u x :=
  oneForm_commutator_pair_of_eval (I := I) cov g Ric u roughDu x hcomm

/-- Scalar Bochner formula, assembled from the realized one-form product rule
and the realized commutator identity for `du`. -/
theorem half_laplacian_gradNormSq_eq
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (h_norm : OneFormNormBochnerAt (I := I) cov g
      (differential1FormFun (I := I) u) roughDu nablaDu x)
    (h_comm : DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x)
    (h_hess : HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have h_norm_fun :
      (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) =
        gradNormSq (I := I) g u := by
    funext y
    exact inner0S_differential1FormFun_eq_gradNormSq (I := I) g u y
  rw [← h_norm_fun]
  rw [h_norm, h_comm, h_hess]
  rw [inner0S_differential1FormFun_pair_eq_grad_inner]
  ring

/-- Fundamental scalar Bochner formula.

This is a clean consumer theorem: it composes the trace product rule, the
pointwise one-form commutator interface, Hessian norm realization, and the
algebraic endpoint. -/
theorem fundamental_bochner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x)
    (hHessComp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have hlapBasis : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInvAt
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond :=
    ScalarLaplacianRealizesTraceAt.toInBasis (I := I) cov g basis gInvAt
      hinv
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond hlap
  have hroughBasis : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInvAt
      (s := 1) (roughDu x) nabla2Du :=
    rough_lap_one_form_realizes_metric_trace (I := I) g basis gInvAt
      nabla2Du (roughDu x) hrough hinv
  refine half_laplacian_gradNormSq_eq (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu x ?_ ?_ ?_
  · exact oneForm_norm_bochner_at (I := I) cov g basis gInvAt hinv
      (differential1FormFun (I := I) u) roughDu nablaDu nabla2Du
      (oneForm_norm_product_rule_of_trace (I := I) cov g basis gInvAt
        (differential1FormFun (I := I) u) nablaDu nabla2Du normSecond hlapBasis htrace)
      hroughBasis
  · exact oneForm_commutator_pair_of_eval (I := I) cov g Ric u roughDu x hcomm
  · exact hessian_norm_realizes_of_nabla_du (I := I) g basis Hess nablaDu hHessComp

/-- Fundamental scalar Bochner formula with the scalar Laplacian trace,
norm-product trace, and Hessian component inputs discharged by named producers.
The one-form commutator remains the primary explicit interface. -/
theorem fundamental_bochner_of_terms
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec Hess x)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I) cov g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu basis gInvAt hinv nabla2Du normSecond
    ?_ ?_ hrough hcomm ?_
  · exact scalar_laplacian_trace_of_hessian (I := I) cov g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond
      (by
        rw [hlapTrace]
        exact metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInvAt
          hinv normSecond Fin.elim0)
  · exact oneForm_norm_second_product_of_metric_compatible (I := I) cov g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I) cov basis X duSec Hess
      nablaDu hfields hHess hnabla

/-- Variant of `fundamental_bochner_of_terms` where the scalar Laplacian trace
of `|du|^2` is produced from a metric-compatible Hessian trace theorem.

This deliberately asks for a realization of the Hessian of the scalar
`|du|^2`; the one-form product-rule tensor `normSecond` alone is not enough to
identify the scalar Laplacian with its metric trace. -/
theorem fundamental_bochner_of_terms_of_normSecond_realizes
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec normDuSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (normSecondSec : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec Hess x)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I) cov normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have hlapIntrinsic : ScalarLaplacianRealizesTraceAt (I := I) cov g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond := by
    simpa [hnormSecond] using
      scalarLaplacianRealizesTraceAt_of_nablaDu (I := I) cov g hmc basis gInvAt
        hinv
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y))
        normDuSec normSecondSec X hfields hnormDu hnormHess hnormGrad
  refine fundamental_bochner (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu basis gInvAt hinv nabla2Du normSecond
    hlapIntrinsic ?_ hrough hcomm ?_
  · exact oneForm_norm_second_product_of_metric_compatible (I := I) cov g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I) cov basis X duSec Hess
      nablaDu hfields hHess hnabla

/-- Geometric wrapper for the fundamental scalar Bochner formula, using the
component Ricci-identity frontier to supply the pointwise commutator interface. -/
theorem fundamental_bochner_of_components
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du)
    (hricciComm : OneFormRicciTraceCommAt (I := I) g Ric u basis gInvAt nabla2Du)
    (hHessComp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu basis gInvAt hinv nabla2Du normSecond
    hlap htrace hrough ?_ hHessComp
  exact oneForm_commutator_eval_of_components (I := I) cov g Ric Rm13 u roughDu
    basis gInvAt duSec nablaDu nablaDuSec nabla2Du
    hinv hRm13 hRic13 hdu hnabla hnabla2 hrough hdlap hricciComm

/-- Levi-Civita-facing scalar Bochner producer.

This removes the direct Ricci trace-commutator input from
`fundamental_bochner_of_components`; the commutator is produced from the
one-form Ricci identity frontier, trailing-slot symmetry, and curvature
skew-adjointness. -/
theorem fundamental_bochner_of_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlap : ScalarLaplacianRealizesTraceAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hHessComp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    (1 / 2 : Real) * laplacian (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_components (I := I)
    (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv duSec nablaDuSec nabla2Du normSecond
    hdu hnabla hnabla2 hlap htrace hrough hdlap ?_ hHessComp
  exact one_form_ricci_trace_comm_of_lc (I := I)
    (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g Ric Rm13 u basis
    gInvAt duSec nablaDu nablaDuSec nabla2Du
    hinv hRm13 hRic13 hdu hnabla hnabla2 hsymm hthird hSkew

/-- Levi-Civita-facing scalar Bochner producer with the scalar Laplacian trace,
norm-product trace, and Hessian component inputs discharged by named producer
wrappers. -/
theorem fundamental_bochner_of_lc_terms
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv duSec nablaDuSec nabla2Du normSecond
    hdu hnabla hnabla2 ?_ ?_ hrough hdlap hsymm hthird hSkew ?_
  · exact scalar_laplacian_trace_of_hessian (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond
      (by
        rw [hlapTrace]
        exact metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInvAt
          hinv normSecond Fin.elim0)
  · exact oneForm_norm_second_product_of_metric_compatible (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) basis X duSec Hess
      nablaDu hfields hHess hnabla

/-- Levi-Civita-facing scalar Bochner producer where the scalar Laplacian trace
of `|du|^2` is supplied by the operator-level metric-compatible Hessian trace
theorem. -/
theorem fundamental_bochner_of_lc_terms_of_normSecond_realizes
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec normDuSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (normSecondSec : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have hlapIntrinsic : ScalarLaplacianRealizesTraceAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond := by
    simpa [hnormSecond] using
      scalarLaplacianRealizesTraceAt_of_nablaDu (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
        basis gInvAt hinv
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y))
        normDuSec normSecondSec X hfields hnormDu hnormHess hnormGrad
  refine fundamental_bochner_of_lc (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv duSec nablaDuSec nabla2Du normSecond
    hdu hnabla hnabla2 hlapIntrinsic ?_ hrough hdlap hsymm hthird hSkew ?_
  · exact oneForm_norm_second_product_of_metric_compatible (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) basis X duSec Hess
      nablaDu hfields hHess hnabla

/-- Levi-Civita-facing scalar Bochner producer with curvature metric skew
discharged from a lowered curvature realization and lowered output skew. -/
theorem fundamental_bochner_of_lc_terms_of_rm04_skew
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hRm04Skew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc_terms (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv X duSec nablaDuSec nabla2Du normSecond
    hfields hHess hdu hnabla hnabla2 hlapTrace hsecond hrough hdlap
    hsymm hthird ?_
  exact rm13MetricSkewAt_of_realizes_outputSkew (I := I) g
    (RicciFlower.LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm13 Rm04
    hRm13 hRm04 hRm04Skew

end Realized
end RicciFlower
