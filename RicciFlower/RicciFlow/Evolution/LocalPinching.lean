import RicciFlower.RicciFlow.Evolution.OdeReduction

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Local Pinching Estimates

MSM110 Chapter 6.5 statement interfaces.

LaTeX labels covered here include `PinchingFor3Manifolds`,
`Ricci-pinching-preserved`, `ricci pinching preserved ineq`,
`d/dt ln (lambda/mu+nu)`, `RicciLowerBound`,
`ricci pinching improves theorem`, `PinchingEstimate-HamiltonForm`,
`f pinching improves evolution`, `DefineP`, `Palpha over Qbeta`,
`f-pinching-evolution`, and `R evolution lambda mu nu`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

variable {M : Type*}

/-- Ordered curvature-operator eigenvalues in dimension three. -/
def CurvatureEigenvaluesOrdered
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), nu t x ≤ mu t x ∧ mu t x ≤ lambda t x

/-- Preservation of the Ricci pinching inequality
`lambda <= C (mu + nu)`. -/
def RicciPinchingPreservedOn
    (lambda mu nu : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M), lambda t x ≤ C * (nu t x + mu t x)

/-- Display `ricci pinching preserved ineq`: `lambda <= C (nu + mu)`. -/
def RicciPinchingPreservedInequalityOn
    (lambda mu nu : Real -> M -> Real) (C : Real) : Prop :=
  RicciPinchingPreservedOn lambda mu nu C

/-- The logarithmic derivative calculation
`d/dt log(lambda/(mu+nu)) <= 0`. -/
def LogPinchingDerivativeNonpositiveOn
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    0 < lambda t x ∧ 0 < mu t x + nu t x ->
      (mu t x ^ 2 * (nu t x - lambda t x) +
        nu t x ^ 2 * (mu t x - lambda t x)) /
          (lambda t x * (nu t x + mu t x)) ≤ 0

/-- Display `d/dt ln (lambda/mu+nu)`, recorded as the corresponding
nonpositive logarithmic derivative calculation. -/
def LogLambdaOverMuPlusNuDerivativeFormulaOn
    (lambda mu nu : Real -> M -> Real) : Prop :=
  LogPinchingDerivativeNonpositiveOn lambda mu nu

/-- Global Ricci lower bound from preserved pinching:
`Rc >= 2 beta^2 R g`. -/
def RicciLowerBoundFromPinchingOn
    (ricciLower scalar : Real -> M -> Real) (beta : Real) : Prop :=
  ∀ (t : Real) (x : M), 2 * beta ^ 2 * scalar t x ≤ ricciLower t x

/-- Decay weight used for the Hamilton pinching estimate.  Mathematically this
is `(nu + mu)^(-delta)` on the positive-curvature region. -/
def PinchingDecayWeightOn
    (lambda mu nu weight : Real -> M -> Real) (delta : Real) : Prop :=
  ∀ (t : Real) (x : M), 0 < delta ∧ 0 ≤ weight t x

/-- Hamilton local pinching estimate in eigenvalue form. -/
def RicciPinchingImprovesOn
    (lambda mu nu weight : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    (lambda t x - nu t x) / (nu t x + mu t x) ≤
      C * weight t x

/-- Display `f pinching improves evolution`, the differential inequality for
Hamilton's improving pinching quantity before it is repackaged. -/
def PinchingImprovesFunctionEvolutionOn
    (f rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), f t x ≤ rhs t x

/-- Hamilton's equivalent trace-free pinching estimate. -/
def HamiltonTracefreePinchingEstimateOn
    (tracefreeRmNormSq scalar weight : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    tracefreeRmNormSq t x / scalar t x ^ 2 ≤ C * weight t x

/-- Algebraic `P` used in the second pinching proof. -/
def pinchingP (lambda mu nu : Real) : Real :=
  lambda ^ 2 * (mu - nu) ^ 2 +
    mu ^ 2 * (lambda - nu) ^ 2 +
    nu ^ 2 * (lambda - mu) ^ 2

/-- Formula `item:define_p`. -/
def PinchingPFormulaOn
    (lambda mu nu P : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    P t x = pinchingP (lambda t x) (mu t x) (nu t x)

/-- Product/quotient parabolic calculation from `lem:palpha_over_qbeta`. -/
def PAlphaOverQBetaFormulaOn
    (phi psi quotient rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), quotient t x = rhs t x ∧ 0 ≤ phi t x ∧ 0 < psi t x

/-- Differential inequality for
`f = R^(epsilon - 2) |Rm^0|^2`. -/
def TracefreeRmPinchingEvolutionInequalityOn
    (f scalar Q : Real -> M -> Real) (epsilon : Real) : Prop :=
  ∀ (t : Real) (x : M),
    0 < scalar t x -> f t x ≤ Q t x + epsilon * scalar t x

/-- Display `R evolution lambda mu nu`, the scalar evolution written in the
curvature-operator eigenvalues. -/
def ScalarEvolutionEigenvalueFormulaOn
    (scalar lambda mu nu rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    rhs t x =
      scalar t x ^ 2 +
        2 * (lambda t x * mu t x + lambda t x * nu t x + mu t x * nu t x)

theorem ricci_pinching_preserved
    (lambda mu nu : Real -> M -> Real) (C : Real)
    (_hode : ∀ x : M, True)
    (_hordered : CurvatureEigenvaluesOrdered lambda mu nu)
    (_hinit : ∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) :
    RicciPinchingPreservedOn lambda mu nu C := by
  sorry

theorem ricci_lower_bound_of_pinching
    (lambda mu nu ricciLower scalar : Real -> M -> Real)
    (C beta : Real)
    (_hpinch : RicciPinchingPreservedOn lambda mu nu C)
    (_hbeta : beta > 0) :
    RicciLowerBoundFromPinchingOn ricciLower scalar beta := by
  sorry

theorem ricci_pinching_improves
    (lambda mu nu : Real -> M -> Real)
    (_hpositiveRicciInitial : Prop) :
    ∃ C delta : Real, ∃ weight : Real -> M -> Real,
      0 < C ∧ 0 < delta ∧ delta < 1 ∧
      PinchingDecayWeightOn lambda mu nu weight delta ∧
      RicciPinchingImprovesOn lambda mu nu weight C := by
  sorry

theorem hamilton_tracefree_pinching_of_eigenvalue_pinching
    (lambda mu nu tracefreeRmNormSq scalar weight : Real -> M -> Real)
    (C : Real)
    (_hpinch : RicciPinchingImprovesOn lambda mu nu weight C) :
    HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C := by
  sorry

theorem palpha_over_qbeta_formula
    (phi psi quotient rhs : Real -> M -> Real)
    (_hphi : ∀ t x, 0 ≤ phi t x)
    (_hpsi : ∀ t x, 0 < psi t x) :
    PAlphaOverQBetaFormulaOn phi psi quotient rhs := by
  sorry

theorem tracefree_rm_pinching_evolution
    (f scalar Q : Real -> M -> Real) (epsilon : Real)
    (_hpq : Prop) :
    TracefreeRmPinchingEvolutionInequalityOn f scalar Q epsilon := by
  sorry

end RicciFlow
end RicciFlower
