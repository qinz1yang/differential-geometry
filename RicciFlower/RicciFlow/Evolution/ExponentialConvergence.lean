import RicciFlower.RicciFlow.Evolution.NormalizedFlow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Exponential Convergence

MSM110 Chapter 6.10 statement interfaces.

Exact LaTeX labels recorded here:
`ExponentialConvergenceToEinstein`, `BoundScalarAbove-1`,
`BoundScalarAbove-2`, `PinchingPreservedForNRF`, `ScalarStaysPositive`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

variable {M : Type*}

def NormalizedUhlenbeckBundleODE
    (iotaRc iota : Real -> M -> Real) (r : Real -> Real) : Prop :=
  ∀ (_t : Real) (_x : M), True

def NormalizedCurvatureOperatorODE
    (lambda mu nu r : Real -> M -> Real) : Prop :=
  ∀ (_t : Real) (_x : M), True

def NormalizedPinchingPreserved
    (lambda mu nu : Real -> M -> Real) (B : Real) : Prop :=
  ∀ t x, lambda t x ≤ B * (mu t x + nu t x)

def NormalizedScalarStaysPositive
    (scalar : Real -> M -> Real) (eps : Real) : Prop :=
  0 < eps ∧ ∀ t x, eps ≤ scalar t x

def ExponentialEigenvaluePinching
    (lambda mu nu decay : Real -> M -> Real) (alpha beta C : Real) : Prop :=
  0 < alpha ∧ alpha < 1 ∧ 0 < beta ∧
    ∀ t x, lambda t x - nu t x ≤ C * (mu t x + nu t x) * decay t x

def ExponentialTracefreeRicciDecay
    (tracefreeRicciNorm decay : Real -> M -> Real) (beta B : Real) : Prop :=
  0 < beta ∧ 0 < B ∧ ∀ t x, tracefreeRicciNorm t x ≤ B * decay t x

def ExponentialConvergenceToEinstein
    (metricDistanceToLimit : Nat -> Real -> Real) (decay : Real -> Real) : Prop :=
  ∀ m : Nat, ∃ B beta : Real, 0 < B ∧ 0 < beta ∧
    ∀ t : Real, metricDistanceToLimit m t ≤ B * decay t

def NormalizedScalarUpperBoundOn
    (scalar : Real -> M -> Real) (A : Real) : Prop :=
  ∀ t x, 0 < scalar t x ∧ scalar t x <= A

def NormalizedAverageScalarUpperBoundOn
    (avgScalar volume : Real -> Real) (A : Real) : Prop :=
  ∀ t : Real, 0 < avgScalar t ∧ avgScalar t <= A * volume t

theorem normalized_pinching_preserved
    (lambda mu nu : Real -> M -> Real)
    (_hpositiveRicciInitial : Prop) :
    ∃ B : Real, NormalizedPinchingPreserved lambda mu nu B := by
  sorry

theorem scalar_stays_positive
    (scalar : Real -> M -> Real)
    (_hpositiveInitial : Prop) :
    ∃ eps : Real, NormalizedScalarStaysPositive scalar eps := by
  sorry

theorem exponential_eigenvalue_pinching
    (lambda mu nu decay : Real -> M -> Real)
    (_hpinching : ∃ B : Real, NormalizedPinchingPreserved lambda mu nu B)
    (_hscalarPositive : Prop) :
    ∃ alpha beta C : Real,
      ExponentialEigenvaluePinching lambda mu nu decay alpha beta C := by
  sorry

theorem exponential_tracefree_ricci_decay
    (lambda mu nu tracefreeRicciNorm decay : Real -> M -> Real)
    (_heigenPinching :
      ∃ alpha beta C : Real,
        ExponentialEigenvaluePinching lambda mu nu decay alpha beta C) :
    ∃ beta B : Real,
      ExponentialTracefreeRicciDecay tracefreeRicciNorm decay beta B := by
  sorry

theorem exponential_convergence_to_einstein
    (metricDistanceToLimit : Nat -> Real -> Real) (decay : Real -> Real)
    (_htracefreeDecay : Prop)
    (_hderivativeEstimates : Prop) :
    ExponentialConvergenceToEinstein metricDistanceToLimit decay := by
  sorry

end RicciFlow
end RicciFlower
