import DifferentialGeometry.Realized.Curvature
import DifferentialGeometry.Coordinates.Tensor
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import DifferentialGeometry.Tensor.RSTensor.Contract
import DifferentialGeometry.Tensor.RSTensor.Field

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Static curvature tensor sections

This file bundles static curvature objects as tensor sections over one
manifold.  It deliberately avoids parameterized metric data and flow
hypotheses.

Future producer route for constructing these sections from a connection:

* use mathlib's `TensorialAt`, `TensorialAt.mkHom`, and `mkHom₂`;
* use the local vector-bundle helper route through
  `ContMDiffVectorBundleHom.ofTensorialAt`;
* prove tensoriality of `connectionRiemannCurvatureField` in the vector-field slots from
  the covariant-derivative laws and Lie-bracket product rules;
* only after those tensoriality and smoothness facts are available, construct
  curvature values in the generic `Tensor13Section` and `Tensor04Section`
  types from the connection.

Until that frontier is closed, this file exposes precise realization predicates
and proves coordinate formulas from bundled tensors by evaluation/unfolding.
-/

noncomputable section

namespace DifferentialGeometry
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Static smooth `(1,3)` tensor section. -/
abbrev Tensor13Section :=
  TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ⊤ 1 3

/-- Static smooth `(0,4)` tensor section. -/
abbrev Tensor04Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ⊤ 4

/-- Static smooth `(0,2)` tensor section. -/
abbrev Tensor02Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ⊤ 2

/-- Pointwise `(0,2)` tensor fiber. -/
abbrev Tensor02At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x

/-- Pointwise `(0,4)` tensor fiber. -/
abbrev Tensor04At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

/-- Pointwise `(1,3)` tensor fiber. -/
abbrev Tensor13At (x : M) :=
  TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x

/-- The unit `(0,0)` tensor used to read a `TensorRSSpace 0 s` as a
covariant `(0,s)` tensor. -/
def scalarOne0S (x : M) : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 0 x :=
  ContinuousMultilinearMap.constOfIsEmpty Real
    (fun _ : Fin 0 => TangentSpace I x) 1

/-- Ricci curvature as the trace of the endomorphism
`X ↦ Rm13(X,Y)Z`, expressed in the realized Hom tensor model by tracing the
leading upper/lower pair of a `(1,3)` tensor. -/
def ricciFromRm13At {x : M} (Rm13 : Tensor13At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
    (scalarOne0S (I := I) x)

/-- Feed two explicit tangent vectors into a `Fin 2` tensor. -/
def vec2 {x : M} (X Y : TangentSpace I x) : Fin 2 -> TangentSpace I x :=
  fun i => if i = 0 then X else Y

/-- Feed three explicit tangent vectors into a `Fin 3` tensor. -/
def vec3 {x : M} (X Y Z : TangentSpace I x) : Fin 3 -> TangentSpace I x :=
  fun i => if i = 0 then X else if i = 1 then Y else Z

/-- Feed four explicit tangent vectors into a `Fin 4` tensor. -/
def vec4 {x : M} (W X Y Z : TangentSpace I x) : Fin 4 -> TangentSpace I x :=
  fun i => if i = 0 then W else if i = 1 then X else if i = 2 then Y else Z

/-- Interpret a bundled Ricci section as a pointwise two-tensor field. -/
def tensor02ToField (Ric : Tensor02Section (I := I) (M := M)) :
    TwoTensorField (I := I) (M := M) :=
  fun x X Y => Ric x (vec2 X Y)

/-- Interpret a bundled lowered Riemann section as a pointwise four-tensor field. -/
def tensor04ToField (Rm04 : Tensor04Section (I := I) (M := M)) :
    FourTensorField (I := I) (M := M) :=
  fun x W X Y Z => Rm04 x (vec4 W X Y Z)

/-- Ricci component in a static frame. -/
def ricciComp
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  Ric x (vec2 (frame i x) (frame j x))

/-- Lowered Riemann component in a static frame. -/
def rm04Comp
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) : Real :=
  Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x))

/-- `(1,3)` Riemann component in a local frame, pairing the output with the
coframe covector. -/
def rm13Comp
    {Idx : Type*} {u : Set M}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (x : M) (a b c d : Idx) : Real :=
  Rm13 x (dualToCotangent (hframe.coeff a x)) (vec3 (frame b x) (frame c x) (frame d x))

/-- Static bundled curvature data.  Smoothness of the scalar field is stored
explicitly; constructing the tensor sections from a connection is a separate
producer theorem frontier. -/
structure CurvatureTensorData where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  scalar : M -> Real
  scalar_smooth : ContMDiff I 𝓘(Real) ⊤ scalar

/-- A bundled `(1,3)` tensor realizes the connection curvature operator after
pairing the output with a covector. -/
def Rm13RealizesConnection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall (X Y Z : TangentField (I := I) (M := M)) (x : M)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x),
      Rm13 x alpha (vec3 (X x) (Y x) (Z x)) =
        cotangentToDual (I := I) alpha ((connectionRiemannCurvatureField (I := I) cov X Y Z) x)

/-- A bundled lowered Riemann tensor realizes `g(R(X,Y)Z,W)`. -/
def Rm04RealizesConnection
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  forall (W X Y Z : TangentField (I := I) (M := M)) (x : M),
    Rm04 x (vec4 (W x) (X x) (Y x) (Z x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov X Y Z) x)

/-- A bundled Ricci tensor is the trace contraction of bundled `(1,3)` Riemann. -/
def RicciTensorRealizesRm13Trace
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall x : M, Ric x = ricciFromRm13At (I := I) (M := M) (Rm13 x)

/-- A bundled Ricci tensor is the frame metric trace of bundled lowered Riemann. -/
def RicciTensorRealizesRm04TraceInFrame
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  Realized.RicciRealizesRm04TraceInFrame (I := I)
    (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame

/-- A scalar curvature function is the frame metric trace of bundled Ricci. -/
def ScalarSectionRealizesRicciTraceInFrame
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  Realized.ScalarRealizesRicciTraceInFrame (I := I)
    scalar (tensor02ToField (I := I) Ric) gInv frame

@[simp]
theorem rm04_comp_eq_eval
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) :
    rm04Comp (I := I) Rm04 frame x i j k l =
      Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x)) :=
  rfl

theorem rm04_comp_eq_connection
    {Idx : Type*}
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm : Rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) Rm04 frame x a b c d =
      g.inner x (frame a x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) := by
  simpa [rm04Comp] using
    hRm (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)
      (fun y => frame d y) x

theorem ricciComp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) Ric frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) Rm04 frame x k i j l := by
  simpa [RicciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    ricciComp, rm04Comp] using
    Realized.ricci_comp_eq_trace (I := I)
      (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame hRic x i j

theorem scalarSection_eq_trace
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) Ric frame x i j := by
  simpa [ScalarSectionRealizesRicciTraceInFrame, tensor02ToField, ricciComp] using
    Realized.scalar_eq_trace (I := I)
      scalar (tensor02ToField (I := I) Ric) gInv frame hScalar x

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) Rm13 frame hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) := by
  simpa [rm13Comp] using
    hRm (fun y => frame b y) (fun y => frame c y) (fun y => frame d y) x
      (dualToCotangent (hframe.coeff a x))

namespace CurvatureTensorData

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (K : CurvatureTensorData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRm : Rm13RealizesConnection (I := I) cov K.rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) K.rm13 frame hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) :=
  DifferentialGeometry.Realized.rm13_comp_eq_connection (I := I) cov K.rm13 frame hframe hRm x a b c d

theorem rm04_comp_eq_connection
    {Idx : Type*}
    (K : CurvatureTensorData (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm : Rm04RealizesConnection (I := I) g cov K.rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) K.rm04 frame x a b c d =
      g.inner x (frame a x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) :=
  DifferentialGeometry.Realized.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x a b c d

theorem ricci_comp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) K.rm04 frame x k i j l :=
  DifferentialGeometry.Realized.ricciComp_eq_trace (I := I) K.ricci K.rm04 gInv frame hRic x i j

theorem ricci_comp_eq_connection_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm : Rm04RealizesConnection (I := I) g cov K.rm04)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          g.inner x (frame k x) ((connectionRiemannCurvatureField (I := I) cov
            (fun y => frame i y) (fun y => frame j y) (fun y => frame l y)) x) := by
  rw [CurvatureTensorData.ricci_comp_eq_trace (I := I) K gInv frame hRic x i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [DifferentialGeometry.Realized.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x k i j l]

theorem scalar_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) K.scalar K.ricci gInv frame)
    (x : M) :
    K.scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) K.ricci frame x i j :=
  DifferentialGeometry.Realized.scalarSection_eq_trace (I := I) K.scalar K.ricci gInv frame hScalar x

end CurvatureTensorData

end Realized
end DifferentialGeometry
