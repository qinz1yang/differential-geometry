import RicciFlower.Curvature.Basic
import RicciFlower.Coordinates.Tensor
import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import RicciFlower.Tensor.RSTensor.Contract
import RicciFlower.Tensor.RSTensor.Field

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Static curvature tensor sections

This file bundles static curvature objects as tensor sections over one
manifold.  It deliberately avoids parameterized metric data and flow
hypotheses.

The connection-to-section producer lives in `RicciFlower.Riemann.Basic` as the
intrinsic `rm13Section`, `rm04Section`, and `ricciSection` constructors.  Their
remaining proof fields are the honest smoothness/tensoriality frontier for
`connectionRiemannCurvatureField`; coordinate files should consume those
sections or their component theorems, not define curvature primitively.

This file contains only tensor aliases, pointwise trace operations, and
component evaluation helpers.  Realization predicates for supplied curvature
sections live in `RicciFlower.Realized.CurvatureTensor`.
-/

noncomputable section

namespace RicciFlower
namespace Curvature

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Static smooth `(1,3)` tensor section. -/
abbrev Tensor13Section :=
  TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 1 3

/-- Static smooth `(0,4)` tensor section. -/
abbrev Tensor04Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 4

/-- Preferred name for a static smooth covariant four-tensor field. -/
abbrev FourTensorField := Tensor04Section (I := I) (M := M)

/-- Static smooth `(0,2)` tensor section. -/
abbrev Tensor02Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 2

/-- Preferred name for a static smooth covariant two-tensor field. -/
abbrev TwoTensorField := Tensor02Section (I := I) (M := M)

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
    RawTwoTensorField (I := I) (M := M) :=
  fun x X Y => Ric x (vec2 X Y)

/-- Interpret a bundled lowered Riemann section as a pointwise four-tensor field. -/
def tensor04ToField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
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
  scalar_smooth : ContMDiff I 𝓘(Real) ∞ scalar

@[simp]
theorem rm04_comp_eq_eval
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) :
    rm04Comp (I := I) Rm04 frame x i j k l =
      Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x)) :=
  rfl

end Curvature
end RicciFlower
