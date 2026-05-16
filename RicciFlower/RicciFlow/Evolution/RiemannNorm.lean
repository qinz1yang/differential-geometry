import RicciFlower.RicciFlow.Evolution.Ricci
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Riemann Curvature Norm Evolution

This file records the fixed-frame component norm of the lowered Riemann tensor
and the finite-sum product-rule evolution of that norm.  The genuinely
geometric simplification from the raw product-rule derivative to the usual
heat equation is kept as an explicit frontier, matching the existing
Ricci-norm architecture.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]

/-- Raise all four indices of a lowered Riemann component family:
`Rm^{abcd} = g^{ap} g^{bq} g^{cr} g^{ds} Rm_pqrs`. -/
def raisedRm04CompInFrame
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    gInv t x a p * gInv t x b q * gInv t x c r * gInv t x d s *
      Realized.rm04Comp (I := I) (Rm04 t) frame x p q r s

@[simp] theorem raisedRm04CompInFrame_apply
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a b c d : Idx) :
    raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d =
      ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
        gInv t x a p * gInv t x b q * gInv t x c r * gInv t x d s *
          Realized.rm04Comp (I := I) (Rm04 t) frame x p q r s := by
  rfl

/-- Fixed-frame squared norm of the lowered Riemann tensor:
`|Rm|^2 = Rm_abcd Rm^{abcd}`. -/
def rm04NormSqInFrame
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      Realized.rm04Comp (I := I) (Rm04 t) frame x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d

@[simp] theorem rm04NormSqInFrame_apply
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    rm04NormSqInFrame (I := I) Rm04 gInv frame t x =
      ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x a b c d *
          raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d := by
  rfl

/-- Nested product-rule RHS for five scalar factors.  The shape is chosen to
match four successive uses of `HasDerivWithinAt.mul`. -/
private def derivProduct5RHS
    (u v w y z du dv dw dy dz : Real) : Real :=
  ((((du * v + u * dv) * w + (u * v) * dw) * y + ((u * v) * w) * dy) * z +
    (((u * v) * w) * y) * dz)

/-- Product-rule RHS for differentiating `Rm^{abcd}`.  The nested shape
intentionally matches repeated uses of `HasDerivWithinAt.mul`. -/
def raisedRm04DerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    derivProduct5RHS
      (gInv t x a p)
      (gInv t x b q)
      (gInv t x c r)
      (gInv t x d s)
      (Realized.rm04Comp (I := I) (Rm04 t) frame x p q r s)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x a p)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x b q)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x c r)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x d s)
      (rm04Dt t x p q r s)

/-- Product-rule RHS for differentiating `|Rm|^2 = Rm_abcd Rm^{abcd}`. -/
def rm04NormDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
    (rm04Dt t x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d +
      Realized.rm04Comp (I := I) (Rm04 t) frame x a b c d *
        raisedRm04DerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          t x a b c d)

/-- The raw product-rule derivative equation for the fixed-frame Riemann norm
square.  This is the narrow finite-sum frontier left after the norm and raw
RHS have been formulated. -/
def Rm04NormRawDerivativeEquationOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rm04NormSqInFrame (I := I) Rm04 gInv frame s x)
      (rm04NormDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x)
      D.carrier
      (t : Real)

/-- Coordinate inner product `<roughDelta Rm, Rm>`. -/
def roughLapRm04InnerInFrame
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      roughLapRm04 t x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d

/-- Coordinate squared norm of `nabla Rm` for lowered Riemann components. -/
def nablaRm04NormSqInFrame
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx,
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
      gInv t x a b *
        gInv t x i p * gInv t x j q * gInv t x k r * gInv t x l s *
          nablaRm04 t x a i j k l * nablaRm04 t x b p q r s

/-- The raw product-rule derivative has simplified to
`2 <roughDelta Rm, Rm> + reaction`.  The reaction term is deliberately
external here because its normal form depends on the chosen Riemann evolution
formula and curvature symmetries. -/
def Rm04NormDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    rm04NormDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x =
      2 * roughLapInner (t : Real) x + reaction (t : Real) x

/-- Time-derivative component identity for `|Rm|^2`. -/
def Rm04NormTimeDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (rmNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rmNormSq s x)
      (2 * roughLapInner (t : Real) x + reaction (t : Real) x)
      D.carrier
      (t : Real)

/-- The time derivative of `|Rm|^2`, reduced to the raw product-rule
derivative and the remaining finite contraction simplification. -/
theorem rm04NormTimeDerivativeComponentsOn_of_rawDerivative
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction) :
    Rm04NormTimeDerivativeComponentsOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      roughLapInner reaction := by
  intro t x
  simpa [h_simplify t x] using h_raw t x

/-- Laplacian component identity for `|Rm|^2`:
`Delta |Rm|^2 = 2 <roughDelta Rm, Rm> + 2 |nabla Rm|^2`. -/
def Rm04NormLaplacianComponentsOn
    (rmNormLap roughLapInner nablaRmNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    rmNormLap t x = 2 * roughLapInner t x + 2 * nablaRmNormSq t x

/-- Heat-equation form for a supplied Riemann norm reaction:
`partial_t |Rm|^2 = Delta |Rm|^2 - 2 |nabla Rm|^2 + reaction`. -/
def Rm04NormHeatEquationOn
    {D : Realized.RealTimeInterval}
    (rmNormSq rmNormLap nablaRmNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rmNormSq s x)
      (rmNormLap (t : Real) x +
        (-2 * nablaRmNormSq (t : Real) x + reaction (t : Real) x))
      D.carrier
      (t : Real)

/-- Algebraic assembly of the Riemann norm heat equation from the
time-derivative and Laplacian component identities. -/
theorem rm04NormHeatEquationOn_of_components
    {D : Realized.RealTimeInterval}
    (rmNormSq rmNormLap roughLapInner nablaRmNormSq reaction : Real -> M -> Real)
    (h_dt : Rm04NormTimeDerivativeComponentsOn
      (D := D) rmNormSq roughLapInner reaction)
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) rmNormSq rmNormLap nablaRmNormSq reaction := by
  intro t x
  have hvalue :
      rmNormLap (t : Real) x +
          (-2 * nablaRmNormSq (t : Real) x + reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x

/-- Riemann norm heat equation assembled from the raw norm derivative, finite
contraction simplification, and the Bochner Laplacian identity for `|Rm|^2`. -/
theorem rm04NormHeatEquationOn_of_rawDerivative
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (rmNormLap roughLapInner nablaRmNormSq reaction : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction)
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap nablaRmNormSq reaction := by
  exact
    rm04NormHeatEquationOn_of_components
      (D := D)
      (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap roughLapInner nablaRmNormSq reaction
      (rm04NormTimeDerivativeComponentsOn_of_rawDerivative
        (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction
        h_raw h_simplify)
      h_lap

end Components

end RicciFlow
end RicciFlower
