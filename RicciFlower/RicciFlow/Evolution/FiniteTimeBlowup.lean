import RicciFlower.RicciFlow.Evolution.LongTimeExistence

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Finite-Time Blowup

MSM110 Chapter 6.8 statement interfaces.

Exact LaTeX labels recorded here:
`FiniteTimeBlowup`, `FiniteTimeSingularity`, `CurvatureBlowup-2`,
`PositiveSectionalPinching`, `RCblowup-lim`, `GlobalPinching-1`,
`GlobalPinching-2`, `SectionalPointwisePinching`,
`UniformConvergenceToEinstein`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

variable {M : Type*}

def FiniteTimeSingularityConclusion (T : Real) : Prop :=
  0 < T

def CurvatureBlowupTwoConclusion
    (curvSup : Real -> Real) (T : Real) : Prop :=
  FiniteTimeSingularityConclusion T ∧
    ∀ K : Real, ∃ t : Real, t < T ∧ K < curvSup t

def PositiveSectionalPinchingConclusion
    (scalarMin scalarMax lambdaMax nuMin : Real -> Real) (T : Real) : Prop :=
  (∃ C gamma : Real, 0 < C ∧ 0 < gamma ∧
    ∀ t : Real, 0 ≤ t -> t < T ->
      1 - C / (scalarMax t + 1) ^ 1 ≤ scalarMin t / scalarMax t) ∧
  (∀ eps : Real, 0 < eps -> eps < 1 ->
    ∃ Teps : Real, Teps < T ∧ ∀ t : Real, Teps ≤ t -> t < T ->
      (1 - eps) * lambdaMax t ≤ nuMin t)

def UniformConvergenceToEinsteinConclusion
    (tracefreeRicciRatio : Real -> Real) (T : Real) : Prop :=
  ∀ eps : Real, 0 < eps -> ∃ tau : Real, tau < T ∧
    ∀ t : Real, tau ≤ t -> t < T -> tracefreeRicciRatio t ≤ eps

def RicciCurvatureBlowupLimitOn
    (ricciMin scalarMax : Real -> Real) (T : Real) : Prop :=
  ∀ eps : Real, 0 < eps -> ∃ tau : Real, tau < T ∧
    ∀ t : Real, tau <= t -> t < T -> (1 - eps) * scalarMax t <= ricciMin t

def GlobalPinchingLowerEstimateOn
    (scalarMin scalarMax decay : Real -> Real) (C : Real) : Prop :=
  ∀ t : Real, scalarMin t / scalarMax t >= 1 - C * decay t

def GlobalPinchingScalarEstimateOn
    (scalar scalarMax : Real -> Real) (eps : Real) : Prop :=
  ∀ t : Real, (1 - eps) * scalarMax t <= scalar t

def SectionalPointwisePinchingOn
    (sectionalMin sectionalMax : Real -> Real) (eps : Real) : Prop :=
  ∀ t : Real, (1 - eps) * sectionalMax t <= sectionalMin t

theorem finite_time_singularity
    (T t0 rho : Real)
    (_hweakMaximumPrinciple : Prop)
    (_hscalarInf : Prop)
    (_hrho : 0 < rho) :
    FiniteTimeSingularityConclusion T := by
  sorry

theorem curvature_blowup_two
    (curvSup : Real -> Real) (T : Real)
    (_hpositiveRicciInitial : Prop)
    (_hfinite : FiniteTimeSingularityConclusion T)
    (_hblowup : CurvatureBlowupAtMaximalTime curvSup T) :
    CurvatureBlowupTwoConclusion curvSup T := by
  sorry

theorem positive_sectional_pinching
    (scalarMin scalarMax lambdaMax nuMin : Real -> Real) (T : Real)
    (_hpositiveRicciInitial : Prop)
    (_hlocalPinching : Prop)
    (_hgradientEstimate : Prop) :
    PositiveSectionalPinchingConclusion scalarMin scalarMax lambdaMax nuMin T := by
  sorry

theorem uniform_convergence_to_einstein
    (tracefreeRicciRatio : Real -> Real) (T : Real)
    (_hpinching : PositiveSectionalPinchingConclusion
      (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 1) T)
    (_hhamiltonPinching : Prop) :
    UniformConvergenceToEinsteinConclusion tracefreeRicciRatio T := by
  sorry

end RicciFlow
end RicciFlower
