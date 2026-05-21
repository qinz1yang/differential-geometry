import RicciFlower.Curvature.Components
import RicciFlower.DimensionThree.RiemannFromRicci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Curvature slot convention checklist

This file centralizes the lightweight convention checks for curvature slots.
It is deliberately downstream from the tensor component layer: tensor-level
component conventions live in `RicciFlower.Tensor.RSTensor.Convention`, while
curvature-specific names such as `Rm13`, `Rm04`, Ricci, and the 3D standard
component convention live here.

Checklist:

* Ricci from `Rm13` is `contract_trace 0 2`, i.e. first upper with first lower.
* `Rm04(W,X,Y,Z)` lowers the output slot of `Rm13`:
  `Rm04(W,X,Y,Z) = Rm13(W_flat)(X,Y,Z)`.
* Lowering the intrinsic Ricci trace gives the first-trace lowered formula
  `Ric_ij = sum_{k,l} gInv k l * Rm04(e_k,e_l,e_i,e_j)`.
  The last-slot trace `Rm04(e_k,e_i,e_j,e_l)` is a legacy compatibility
  orientation and should not be used silently in Lemma 6.3.
* A realized lowered curvature tensor satisfies
  `Rm04(W,X,Y,Z) = g(W, R(X,Y)Z)`.
* The 3D algebra adapter uses
  `standardRmCompAt i j k l = rm04CompAt l i j k`.
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
variable {x : M}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Checklist item: Ricci is the first-upper/first-lower trace of `Rm13`. -/
@[simp]
theorem ricciFromRm13At_eq_contract_trace
    (Rm13 : Tensor13At (I := I) (M := M) x) :
    ricciFromRm13At (I := I) (M := M) Rm13 =
      (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        (scalarOne0S (I := I) x) := by
  rfl

/-- Checklist item: `Rm04` lowers the output slot of `Rm13`. -/
theorem rm04LowersRm13At_convention
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (h : Realized.Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (W X Y Z : TangentSpace I x) :
    Rm04 (vec4 W X Y Z) =
      Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z) :=
  h W X Y Z

/-- Checklist item: lowering the intrinsic `Rm13` Ricci trace gives the
first-trace `Rm04` component orientation. -/
theorem ricciFromRm13At_rm04_first_trace_convention
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Realized.Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (hInvSym : forall a b : Idx, gInv a b = gInv b a)
    (i j : Idx) :
    Realized.ricciCompAt (I := I) basis
        (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Realized.rm04CompAt (I := I) basis Rm04 k l i j := by
  have h := Realized.ricciFromRm13_comp_eq_rm04_trace
    (I := I) g basis gInv hinv Rm13 Rm04 hLower i j
  rw [h]
  calc
    (∑ a : Idx, ∑ k : Idx,
        gInv a k * Realized.rm04CompAt (I := I) basis Rm04 k a i j)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv a k * Realized.rm04CompAt (I := I) basis Rm04 k a i j := by
        rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Realized.rm04CompAt (I := I) basis Rm04 k l i j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hInvSym l k]

end Curvature

namespace Realized

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Checklist item: realized `Rm04` uses
`Rm04(W,X,Y,Z) = g(W, R(X,Y)Z)`. -/
theorem rm04RealizesConnection_convention
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (h : Rm04RealizesConnection (I := I) g cov Rm04)
    (W X Y Z : SmoothTangentSection (I := I) (M := M)) (x : M) :
    Rm04 x (vec4 (W x) (X x) (Y x) (Z x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov X Y Z) x) :=
  h W X Y Z x

end Realized

namespace DimensionThree

open Realized
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}

/-- Checklist item: the 3D standard algebra convention is the RicciFlower
lowered Riemann slot permutation `R i j k l = Rm04(e_l,e_i,e_j,e_k)`. -/
@[simp]
theorem standardRmCompAt_slot_convention
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (i j k l : Fin 3) :
    standardRmCompAt (I := I) basis Rm04 i j k l =
      rm04CompAt (I := I) basis Rm04 l i j k := by
  rfl

end DimensionThree

end RicciFlower
