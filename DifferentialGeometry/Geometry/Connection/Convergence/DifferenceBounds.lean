import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

def ConnectionDifferenceFieldRealizes
    (g h : SmoothRiemannianMetric I M)
    (D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2) : Prop :=
  forall x : M,
    D x =
      Tensor0SBundle.connectionDifferenceTensorAt
        (I := I)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) h) x

noncomputable def connectionDifferenceDerivNorm
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2))
    (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) 1 (k + 2) (Dk x))

def ConnectionDifferenceDerivRealizes
    (g h : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2)) : Prop :=
  exists D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2,
    ConnectionDifferenceFieldRealizes (I := I) g h D ∧
      Tensor0SBundle.HigherCovDerivRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) h) D k Dk

def ConnectionDifferenceDerivBoundOn
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) :
    Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnectionDifferenceDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connectionDifferenceDerivNorm (I := I) g k Dk x <= C

def ConnectionDifferenceEpsBoundOn
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) : Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnectionDifferenceDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connectionDifferenceDerivNorm (I := I) g k Dk x <= C * eps

def ConnectionDifferenceEpsBoundsBelow
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnectionDifferenceEpsBoundOn (I := I) K eps g h k (C k)

def connectionDifferenceOneConst (Idx : Type*) [Fintype Idx] : Real :=
  let n : Real := Fintype.card Idx
  let q : Real := n * (((n * (n * 8)) * (3 * 8))) + n * (3 * 16)
  Real.sqrt
    ((Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 3 -> Idx) : Real) * q ^ 2))

def connectionDifferenceTwoConst (Idx : Type*) [Fintype Idx] : Real :=
  let n : Real := Fintype.card Idx
  let Q0 : Real := n * (n * 8)
  let R0 : Real := n * (n * (16 + Q0 * 8 + Q0 * 8))
  let q : Real :=
    n * (Q0 * (3 * 16) + R0 * (3 * 8)) +
      n * (3 * 32 + Q0 * (3 * 16))
  Real.sqrt
    ((Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 4 -> Idx) : Real) * q ^ 2))

def connectionDifferenceEpsConstTwo
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace Real E]
    : Nat -> Real
  | 0 => 12
  | _ + 1 => connectionDifferenceOneConst (Fin (Module.finrank Real E))

def connectionDifferenceEpsConstThree
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace Real E]
    : Nat -> Real
  | 0 => 12
  | 1 => connectionDifferenceOneConst (Fin (Module.finrank Real E))
  | _ => connectionDifferenceTwoConst (Fin (Module.finrank Real E))

def connectionDifferenceCoeff (eps : Real) : Real :=
  (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)

end FixedDomain

end HCGCompactness
end DifferentialGeometry
