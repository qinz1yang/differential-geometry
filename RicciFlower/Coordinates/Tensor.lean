import RicciFlower.Coordinates.Basic
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.Tensor.RSTensor.Components
import RicciFlower.Tensor.RSTensor.Basis
import RicciFlower.Tensor.RSTensor.CotangentRiemannian

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

set_option backward.isDefEq.respectTransparency false in
/-- On the coordinate-frame domain, the fixed tensor-bundle basis section
`Tensor0SSpace.constInChart` is the basis tensor of the coordinate local frame.

This lower coordinate-tensor normalization lets `(0,s)` coordinate derivative
proofs use fixed-chart covectors without importing the mixed-tensor input
expansion file. -/
theorem constInChart_eq_basis0S_coordFrame {r : Nat}
    [IsManifold I ∞ M]
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) :
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) x =
      Tensor0SBundle.basisTensor0S (I := I)
        (coordinateFrameAt_basis (I := I) x₀ hx) upper := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hxE : x ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [Tensor0SBundle.Tensor0SSpace.constInChart]
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (F := E) (E := TangentSpace I) x₀ x hxE]
  ext v
  simp [Tensor0SBundle.basisTensor0S, Tensor0SBundle.tensor0SBasis,
    Tensor0SBundle.continuousMultilinearMapBasis_apply,
    Tensor0SBundle.continuousMultilinearMapBasisElem, continuousMultilinearMap_basis,
    continuousMultilinearMap_basisElem, Tensor0SBundle.coframeOfBasis,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    basisRepr_eq_triv, coordinateTrivializationAt]

/-- At the chart center, a fixed-chart coordinate covector evaluates as the
coordinate-frame coefficient functional. -/
theorem constInChart_one_eval_coordCoeff
    [IsManifold I ∞ M]
    (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E)
    (W : TangentSpace I x₀) :
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) 1 x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) 1) (fun _ : Fin 1 => i)) x₀
        (fun _ : Fin 1 => W) =
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x₀ W := by
  have hconst :=
    constInChart_eq_basis0S_coordFrame (𝕜 := 𝕜) (I := I) (M := M)
      (r := 1) x₀ (coordinateFrameAt_mem (I := I) x₀) (fun _ : Fin 1 => i)
  calc
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) 1 x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) 1) (fun _ : Fin 1 => i)) x₀
        (fun _ : Fin 1 => W)
        =
      Tensor0SBundle.basisTensor0S (I := I)
        (coordinateFrameAt_basis (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀))
        (fun _ : Fin 1 => i) (fun _ : Fin 1 => W) := by
        rw [hconst]
    _ = (coordinateFrameAt_toBasis (I := I) x₀).coord i W := by
      simp [coordinateFrameAt_toBasis, Tensor0SBundle.basisTensor0S_apply]
    _ = (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x₀ W := by
      exact (coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x₀ W i).symm

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

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle Module
open scoped Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
  {n : WithTop ℕ∞}
  {u : Set M}

/-- The local-frame coframe covector is the one-slot covariant basis tensor at
points of the frame domain. -/
theorem coframe_eq_basis0S
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    {x : M} (hx : x ∈ u) (i : Idx) :
    Tensor0SBundle.dualToCotangent (I := I)
        (coframeInFrame frame hframe x i) =
      Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx)
        (fun _ : Fin 1 => i) := by
  apply Tensor0SBundle.cotangentToDualLinear_injective (I := I)
  ext v
  simp [coframeInFrame, Tensor0SBundle.basisTensor0S_apply,
    IsLocalFrameOn.coeff, hx]

end

end Coordinates
end RicciFlower
