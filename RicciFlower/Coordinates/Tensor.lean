import RicciFlower.Coordinates.Basic
import RicciFlower.Tensor.RSTensor.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Local-Frame Tensor Components

This file evaluates realized tensor fibers against mathlib local frames.  The
legacy component API evaluates directly on frame fields.  The preferred
domain-aware API below evaluates through the pointwise basis
`hframe.toBasisAt hx`, using the standard `component0S` and `componentRS`
wrappers from the tensor layer.
-/

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {n : WithTop ℕ∞}
  {u : Set M}

/-- A pointwise realized covariant tensor field on tangent spaces. -/
abbrev FrameTensor0SField (s : Nat) :=
  (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := 𝕜) s I x

/-- A pointwise realized mixed tensor field in the `RSTensor` representation. -/
abbrev FrameTensorRSField (r s : Nat) :=
  (x : M) -> Tensor0SBundle.TensorRSSpace (𝕜 := 𝕜) r s I x

/-- The dual coframe covector supplied by a local frame. -/
def coframeInFrame
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (i : Idx) : TangentSpace I x →ₗ[𝕜] 𝕜 :=
  hframe.coeff i x

@[simp] theorem coframeInFrame_apply
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (i : Idx) (v : TangentSpace I x) :
    coframeInFrame frame hframe x i v = hframe.coeff i x v := by
  rfl

/-- Component of a realized `(0,s)` tensor field in a local frame. -/
def tensor0SComponentInFrame {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E n frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) : 𝕜 :=
  T x (fun a => frame (vectorSlots a) x)

@[simp] theorem tensor0SComponentInFrame_eval {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensor0SComponentInFrame T frame hframe x vectorSlots =
      T x (fun a => frame (vectorSlots a) x) := by
  rfl

/-- Component of a realized `(0,s)` tensor field in a local frame at a point in
the frame domain.

Prefer this domain-aware wrapper in new coordinate proofs.  It uses the
pointwise basis supplied by `hframe.toBasisAt hx`, so downstream proofs do not
need to unfold the local-frame implementation. -/
def tensor0SComponentInFrameAt {s : Nat} [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (slots : Fin s -> Idx) : 𝕜 :=
  Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx) (T x) slots

@[simp] theorem tensor0SComponentInFrameAt_eval {s : Nat}
    [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (slots : Fin s -> Idx) :
    tensor0SComponentInFrameAt T frame hframe x hx slots =
      T x (fun a => hframe.toBasisAt hx (slots a)) := by
  rfl

/-- Component of a realized mixed tensor after supplying its covariant input. -/
def tensorRSComponentFromCovariantInputInFrame {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := 𝕜) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E n frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) : 𝕜 :=
  (T x (input x)) (fun a => frame (vectorSlots a) x)

@[simp] theorem tensorRSComponentFromCovariantInputInFrame_eval {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := 𝕜) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensorRSComponentFromCovariantInputInFrame T input frame hframe x vectorSlots =
      (T x (input x)) (fun a => frame (vectorSlots a) x) := by
  rfl

/-- Component of a realized mixed `(r,s)` tensor field in a local frame at a
point in the frame domain.

The upper indices are handled by the standard tensor-layer `componentRS` API.
This keeps the Hom implementation and `basisTensor0S` hidden from downstream
coordinate proofs. -/
def tensorRSComponentInFrame {r s : Nat} [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : 𝕜 :=
  Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx) (T x) upper lower

@[simp] theorem tensorRSComponentInFrame_eval {r s : Nat}
    [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    tensorRSComponentInFrame T frame hframe x hx upper lower =
      Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx) (T x) upper lower := by
  rfl

@[simp] theorem tensorRSComponentInFrame_apply {r s : Nat}
    [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    tensorRSComponentInFrame T frame hframe x hx upper lower =
      (T x
        (Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx) upper))
        (fun a => hframe.toBasisAt hx (lower a)) := by
  rfl

/-- Two lower component slots. -/
def slots2 (i j : Idx) : Fin 2 -> Idx :=
  fun q => if q = 0 then i else j

/-- Three lower component slots. -/
def slots3 (i j k : Idx) : Fin 3 -> Idx :=
  fun q => if q = 0 then i else if q = 1 then j else k

/-- Four lower component slots. -/
def slots4 (i j k l : Idx) : Fin 4 -> Idx :=
  fun q => if q = 0 then i else if q = 1 then j else if q = 2 then k else l

@[simp] theorem slots2_zero (i j : Idx) :
    slots2 i j 0 = i := by
  simp [slots2]

@[simp] theorem slots2_one (i j : Idx) :
    slots2 i j 1 = j := by
  simp [slots2]

@[simp] theorem slots3_zero (i j k : Idx) :
    slots3 i j k 0 = i := by
  simp [slots3]

@[simp] theorem slots3_one (i j k : Idx) :
    slots3 i j k 1 = j := by
  simp [slots3]

@[simp] theorem slots3_two (i j k : Idx) :
    slots3 i j k 2 = k := by
  simp [slots3]

@[simp] theorem slots4_zero (i j k l : Idx) :
    slots4 i j k l 0 = i := by
  simp [slots4]

@[simp] theorem slots4_one (i j k l : Idx) :
    slots4 i j k l 1 = j := by
  simp [slots4]

@[simp] theorem slots4_two (i j k l : Idx) :
    slots4 i j k l 2 = k := by
  simp [slots4]

@[simp] theorem slots4_three (i j k l : Idx) :
    slots4 i j k l 3 = l := by
  simp [slots4]

/-- Single upper component index. -/
def upperIdx1 (k : Idx) : Fin 1 -> Idx :=
  fun _ => k

/-- Two lower component indices. -/
def lowerIdx2 (i j : Idx) : Fin 2 -> Idx :=
  slots2 i j

@[simp] theorem upperIdx1_apply (k : Idx) (q : Fin 1) :
    upperIdx1 k q = k := by
  rfl

@[simp] theorem lowerIdx2_zero (i j : Idx) :
    lowerIdx2 i j 0 = i := by
  simp [lowerIdx2]

@[simp] theorem lowerIdx2_one (i j : Idx) :
    lowerIdx2 i j 1 = j := by
  simp [lowerIdx2]

@[simp] theorem Function_update_upperIdx1
    (k m : Idx) (a : Fin 1) :
    Function.update (upperIdx1 k) a m = upperIdx1 m := by
  fin_cases a
  funext q
  fin_cases q
  simp [upperIdx1]

@[simp] theorem Function_update_lowerIdx2_zero
    (i j m : Idx) :
    Function.update (lowerIdx2 i j) 0 m = lowerIdx2 m j := by
  funext q
  fin_cases q <;> simp [lowerIdx2]

@[simp] theorem Function_update_lowerIdx2_one
    (i j m : Idx) :
    Function.update (lowerIdx2 i j) 1 m = lowerIdx2 i m := by
  funext q
  fin_cases q <;> simp [lowerIdx2]

/-- `(0,2)` tensor component in a local frame. -/
def tensor02CompInFrame [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensor0SField (I := I) (M := M) 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j : Idx) : 𝕜 :=
  tensor0SComponentInFrameAt T frame hframe x hx (slots2 i j)

@[simp] theorem tensor02CompInFrame_eval [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensor0SField (I := I) (M := M) 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    tensor02CompInFrame T frame hframe x hx i j =
      T x (fun a => hframe.toBasisAt hx (slots2 i j a)) := by
  rfl

/-- `(0,4)` tensor component in a local frame. -/
def tensor04CompInFrame [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensor0SField (I := I) (M := M) 4)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j k l : Idx) : 𝕜 :=
  tensor0SComponentInFrameAt T frame hframe x hx (slots4 i j k l)

@[simp] theorem tensor04CompInFrame_eval [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensor0SField (I := I) (M := M) 4)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j k l : Idx) :
    tensor04CompInFrame T frame hframe x hx i j k l =
      T x (fun a => hframe.toBasisAt hx (slots4 i j k l a)) := by
  rfl

/-- `(1,2)` tensor component in a local frame. -/
def tensor12CompInFrame [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) 1 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (k i j : Idx) : 𝕜 :=
  tensorRSComponentInFrame T frame hframe x hx (upperIdx1 k) (lowerIdx2 i j)

@[simp] theorem tensor12CompInFrame_eval [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) 1 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (k i j : Idx) :
    tensor12CompInFrame T frame hframe x hx k i j =
      (T x
        (Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx) (upperIdx1 k)))
        (fun a => hframe.toBasisAt hx (lowerIdx2 i j a)) := by
  rfl

/-- `(1,3)` tensor component in a local frame. -/
def tensor13CompInFrame [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) 1 3)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (a i j k : Idx) : 𝕜 :=
  tensorRSComponentInFrame T frame hframe x hx (upperIdx1 a) (slots3 i j k)

@[simp] theorem tensor13CompInFrame_eval [Fintype Idx] [DecidableEq Idx]
    (T : FrameTensorRSField (I := I) (M := M) 1 3)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (a i j k : Idx) :
    tensor13CompInFrame T frame hframe x hx a i j k =
      (T x
        (Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx) (upperIdx1 a)))
        (fun q => hframe.toBasisAt hx (slots3 i j k q)) := by
  rfl

end

end Coordinates
end RicciFlower
