import DifferentialGeometry.Realized.CurvatureComponents
import DifferentialGeometry.Realized.RoughLaplacian
import DifferentialGeometry.Realized.LeviCivita.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bianchi Identity Interfaces

This file records the realized tensor statements for first Bianchi, second
Bianchi, and contracted Bianchi.  The identities are stated on bundled or
pointwise tensors; constructing the relevant curvature and covariant-derivative
tensors from a connection is kept as a separate producer frontier.
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

/-- Feed five explicit tangent vectors into a `Fin 5` tensor.  For a covariant
derivative of a `(0,4)` tensor, the first slot is the derivative direction. -/
def vec5 {x : M} (A B C D F : TangentSpace I x) :
    Fin 5 -> TangentSpace I x :=
  fun i =>
    if i = 0 then A
    else if i = 1 then B
    else if i = 2 then C
    else if i = 3 then D
    else F

/-- First Bianchi identity for a lowered Riemann tensor:
`R(W,X,Y,Z) + R(W,Y,Z,X) + R(W,Z,X,Y) = 0`. -/
def FirstBianchiAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  ∀ W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) + Rm04 (vec4 W Y Z X) + Rm04 (vec4 W Z X Y) = 0

theorem first_bianchi {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (h : FirstBianchiAt (I := I) Rm04)
    (W X Y Z : TangentSpace I x) :
    Rm04 (vec4 W X Y Z) + Rm04 (vec4 W Y Z X) + Rm04 (vec4 W Z X Y) = 0 :=
  h W X Y Z

/-- Section-level first Bianchi identity. -/
def FirstBianchiSection (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  ∀ x : M, FirstBianchiAt (I := I) (Rm04 x)

theorem first_bianchi_apply
    (Rm04 : Tensor04Section (I := I) (M := M))
    (h : FirstBianchiSection (I := I) Rm04)
    (x : M) (W X Y Z : TangentSpace I x) :
    Rm04 x (vec4 W X Y Z) + Rm04 x (vec4 W Y Z X) +
      Rm04 x (vec4 W Z X Y) = 0 :=
  h x W X Y Z

/-- Second Bianchi identity for the covariant derivative of lowered Riemann.
The tensor slots are `(derivative, W, X, Y, Z)`. -/
def SecondBianchiAt {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ A W X Y Z : TangentSpace I x,
    nablaRm04 (vec5 A W X Y Z) +
      nablaRm04 (vec5 X W Y A Z) +
        nablaRm04 (vec5 Y W A X Z) = 0

theorem second_bianchi {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : SecondBianchiAt (I := I) nablaRm04)
    (A W X Y Z : TangentSpace I x) :
    nablaRm04 (vec5 A W X Y Z) +
      nablaRm04 (vec5 X W Y A Z) +
        nablaRm04 (vec5 Y W A X Z) = 0 :=
  h A W X Y Z

/-- Section-level second Bianchi identity. -/
def SecondBianchiSection
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ x : M, SecondBianchiAt (I := I) (nablaRm04 x)

theorem second_bianchi_apply
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : SecondBianchiSection (I := I) nablaRm04)
    (x : M) (A W X Y Z : TangentSpace I x) :
    nablaRm04 x (vec5 A W X Y Z) +
      nablaRm04 x (vec5 X W Y A Z) +
        nablaRm04 x (vec5 Y W A X Z) = 0 :=
  h x A W X Y Z

/-- Contracted second Bianchi in a tangent basis:
`div Ric = (1/2) d scalar`.  The slots of `nablaRic` are
`(derivative, first Ricci slot, second Ricci slot)`. -/
def ContractedBianchiAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ X : TangentSpace I x,
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nablaRic (vec3 (basis i) (basis j) X)) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X)

theorem contracted_bianchi
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (h : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nablaRic (vec3 (basis i) (basis j) X)) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) :=
  h X

/-- Explicit bridge saying that a second-Bianchi proof supplies the contracted
Bianchi identity after the metric trace and Ricci/scalar trace reductions have
been performed.  This keeps the hard contraction proof as a named producer. -/
def ContractedBianchiOfSecondAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  SecondBianchiAt (I := I) nablaRm04 ->
    ContractedBianchiAt (I := I) basis gInv nablaRic dScalar

theorem contracted_bianchi_of_second
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hcontract : ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
      nablaRic dScalar)
    (hsecond : SecondBianchiAt (I := I) nablaRm04) :
    ContractedBianchiAt (I := I) basis gInv nablaRic dScalar :=
  hcontract hsecond

end Realized
end DifferentialGeometry
