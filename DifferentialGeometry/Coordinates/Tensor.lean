import DifferentialGeometry.Coordinates.Basic
import DifferentialGeometry.Tensor.RSTensor.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# DifferentialGeometry Local-Frame Tensor Components

This file evaluates realized tensor fibers against mathlib local frames.  The
core direct component API is for covariant `(0,s)` tensors.  Mixed `(r,s)`
tensors in the vendored `RSTensor` model are represented as maps from a
covariant `r`-tensor input to a covariant `s`-tensor output, so mixed components
are exposed only after that covariant input is supplied explicitly.
-/

namespace DifferentialGeometry
namespace Coordinates

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {u : Set M}

/-- A pointwise realized covariant tensor field on tangent spaces. -/
abbrev FrameTensor0SField (s : Nat) :=
  (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := Real) s I x

/-- A pointwise realized mixed tensor field in the `RSTensor` representation. -/
abbrev FrameTensorRSField (r s : Nat) :=
  (x : M) -> Tensor0SBundle.TensorRSSpace (𝕜 := Real) r s I x

/-- The dual coframe covector supplied by a local frame. -/
def coframeInFrame
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i : Idx) : TangentSpace I x →ₗ[Real] Real :=
  hframe.coeff i x

@[simp] theorem coframeInFrame_apply
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i : Idx) (v : TangentSpace I x) :
    coframeInFrame frame hframe x i v = hframe.coeff i x v := by
  rfl

/-- Component of a realized `(0,s)` tensor field in a local frame. -/
def tensor0SComponentInFrame {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) : Real :=
  T x (fun a => frame (vectorSlots a) x)

@[simp] theorem tensor0SComponentInFrame_eval {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensor0SComponentInFrame T frame hframe x vectorSlots =
      T x (fun a => frame (vectorSlots a) x) := by
  rfl

/-- Component of a realized mixed tensor after supplying its covariant input. -/
def tensorRSComponentFromCovariantInputInFrame {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := Real) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) : Real :=
  (T x (input x)) (fun a => frame (vectorSlots a) x)

@[simp] theorem tensorRSComponentFromCovariantInputInFrame_eval {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := Real) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensorRSComponentFromCovariantInputInFrame T input frame hframe x vectorSlots =
      (T x (input x)) (fun a => frame (vectorSlots a) x) := by
  rfl

end

end Coordinates
end DifferentialGeometry
