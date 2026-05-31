import RicciFlower.Curvature.Tensor
import RicciFlower.Realized.Curvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Realized curvature tensor wrappers

This file keeps realization predicates and compatibility wrappers for bundled
curvature tensors.  The tensor aliases, pointwise trace, vector-slot helpers,
and bundled curvature data live in `RicciFlower.Curvature.Tensor`.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev Tensor13Section := RicciFlower.Curvature.Tensor13Section (I := I) (M := M)
abbrev Tensor04Section := RicciFlower.Curvature.Tensor04Section (I := I) (M := M)
abbrev Tensor02Section := RicciFlower.Curvature.Tensor02Section (I := I) (M := M)
abbrev Tensor02At (x : M) := RicciFlower.Curvature.Tensor02At (I := I) (M := M) x
abbrev Tensor04At (x : M) := RicciFlower.Curvature.Tensor04At (I := I) (M := M) x
abbrev Tensor13At (x : M) := RicciFlower.Curvature.Tensor13At (I := I) (M := M) x
abbrev scalarOne0S (x : M) := RicciFlower.Curvature.scalarOne0S (I := I) x
abbrev ricciFromRm13At {x : M} (Rm13 : Tensor13At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  RicciFlower.Curvature.ricciFromRm13At (I := I) (M := M) Rm13
abbrev vec2 {x : M} (X Y : TangentSpace I x) : Fin 2 -> TangentSpace I x :=
  RicciFlower.Curvature.vec2 (I := I) X Y
abbrev vec3 {x : M} (X Y Z : TangentSpace I x) : Fin 3 -> TangentSpace I x :=
  RicciFlower.Curvature.vec3 (I := I) X Y Z
abbrev vec4 {x : M} (W X Y Z : TangentSpace I x) : Fin 4 -> TangentSpace I x :=
  RicciFlower.Curvature.vec4 (I := I) W X Y Z
abbrev tensor02ToField (Ric : Tensor02Section (I := I) (M := M)) :
    RawTwoTensorField (I := I) (M := M) :=
  RicciFlower.Curvature.tensor02ToField (I := I) Ric
abbrev tensor04ToField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  RicciFlower.Curvature.tensor04ToField (I := I) Rm04
abbrev ricciComp {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  RicciFlower.Curvature.ricciComp (I := I) Ric frame x i j
abbrev rm04Comp {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) : Real :=
  RicciFlower.Curvature.rm04Comp (I := I) Rm04 frame x i j k l
abbrev rm13Comp {Idx : Type*} {u : Set M}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (x : M) (a b c d : Idx) : Real :=
  RicciFlower.Curvature.rm13Comp (I := I) Rm13 frame hframe x a b c d
abbrev CurvatureTensorData := RicciFlower.Curvature.CurvatureTensorData (I := I) (M := M)

/-- Smooth tangent sections used by curvature-realization predicates. -/
abbrev SmoothTangentSection :=
  ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)

/-- A bundled `(1,3)` tensor realizes the connection curvature operator after
pairing the output with a covector, on smooth tangent sections.

The smooth-section restriction is essential: Mathlib's covariant-derivative
axioms only control differentiable sections.  Raw dependent functions
`(x : M) -> TangentSpace I x` are not a valid realization interface for
connection curvature. -/
def Rm13RealizesConnection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall (X Y Z : SmoothTangentSection (I := I) (M := M)) (x : M)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x),
      Rm13 x alpha (vec3 (X x) (Y x) (Z x)) =
        cotangentToDual (I := I) alpha
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)

/-- A bundled lowered Riemann tensor realizes `g(R(X,Y)Z,W)` on smooth tangent
sections. -/
def Rm04RealizesConnection
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  forall (X Y Z W : SmoothTangentSection (I := I) (M := M)) (x : M),
    Rm04 x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)

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
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : Rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) Rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x) := by
  simpa [rm04Comp] using
    hRm (frame a) (frame b) (frame c) (frame d) x

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
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) Rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) := by
  simpa [rm13Comp] using
    hRm (frame b) (frame c) (frame d) x (dualToCotangent (hframe.coeff a x))

namespace CurvatureTensorData

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (K : CurvatureTensorData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : Rm13RealizesConnection (I := I) cov K.rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) K.rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) :=
  RicciFlower.Realized.rm13_comp_eq_connection (I := I) cov K.rm13 frame hframe hRm x a b c d

theorem rm04_comp_eq_connection
    {Idx : Type*}
    (K : CurvatureTensorData (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : Rm04RealizesConnection (I := I) g cov K.rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) K.rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x) :=
  RicciFlower.Realized.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x a b c d

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
  RicciFlower.Realized.ricciComp_eq_trace (I := I) K.ricci K.rm04 gInv frame hRic x i j

theorem ricci_comp_eq_connection_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : Rm04RealizesConnection (I := I) g cov K.rm04)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv
      (fun i y => frame i y))
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci (fun i y => frame i y) x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          g.inner x (frame l x) ((connectionRiemannCurvatureField (I := I) cov
            (fun y => frame k y) (fun y => frame i y) (fun y => frame j y)) x) := by
  rw [CurvatureTensorData.ricci_comp_eq_trace (I := I) K gInv
    (fun i y => frame i y) hRic x i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [RicciFlower.Realized.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x k i j l]

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
  RicciFlower.Realized.scalarSection_eq_trace (I := I) K.scalar K.ricci gInv frame hScalar x

end CurvatureTensorData

end Realized
end RicciFlower
