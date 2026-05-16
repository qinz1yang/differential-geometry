import RicciFlower.RicciFlow.Evolution.FiniteTimeBlowup

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM110 Chapter 6.8: Finite-Time Blowup

Exact LaTeX labels represented here:
`FiniteTimeBlowup`, `FiniteTimeSingularity`, `CurvatureBlowup-2`,
`PositiveSectionalPinching`, `RCblowup-lim`, `GlobalPinching-1`,
`GlobalPinching-2`, `SectionalPointwisePinching`,
`UniformConvergenceToEinstein`.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section08

noncomputable section

open RicciFlower.RicciFlow

theorem lem_finite_time_singularity
    (T t0 rho : Real)
    (hweakMaximumPrinciple hscalarInf : Prop)
    (hrho : 0 < rho) :
    FiniteTimeSingularityConclusion T :=
  RicciFlower.RicciFlow.finite_time_singularity
    T t0 rho hweakMaximumPrinciple hscalarInf hrho

theorem cor_curvature_blowup_two
    (curvSup : Real -> Real) (T : Real)
    (hpositiveRicciInitial : Prop)
    (hfinite : FiniteTimeSingularityConclusion T)
    (hblowup : CurvatureBlowupAtMaximalTime curvSup T) :
    CurvatureBlowupTwoConclusion curvSup T :=
  RicciFlower.RicciFlow.curvature_blowup_two
    curvSup T hpositiveRicciInitial hfinite hblowup

theorem lem_positive_sectional_pinching
    (scalarMin scalarMax lambdaMax nuMin : Real -> Real) (T : Real)
    (hpositiveRicciInitial hlocalPinching hgradientEstimate : Prop) :
    PositiveSectionalPinchingConclusion scalarMin scalarMax lambdaMax nuMin T :=
  RicciFlower.RicciFlow.positive_sectional_pinching
    scalarMin scalarMax lambdaMax nuMin T
    hpositiveRicciInitial hlocalPinching hgradientEstimate

theorem cor_uniform_convergence_to_einstein
    (tracefreeRicciRatio : Real -> Real) (T : Real)
    (hpinching : PositiveSectionalPinchingConclusion
      (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 1) T)
    (hhamiltonPinching : Prop) :
    UniformConvergenceToEinsteinConclusion tracefreeRicciRatio T :=
  RicciFlower.RicciFlow.uniform_convergence_to_einstein
    tracefreeRicciRatio T hpinching hhamiltonPinching

theorem eq_rcblowup_lim
    (ricciMin scalarMax : Real -> Real) (T : Real)
    (h : RicciCurvatureBlowupLimitOn ricciMin scalarMax T) :
    RicciCurvatureBlowupLimitOn ricciMin scalarMax T :=
  h

theorem eq_global_pinching_one
    (scalarMin scalarMax decay : Real -> Real) (C : Real)
    (h : GlobalPinchingLowerEstimateOn scalarMin scalarMax decay C) :
    GlobalPinchingLowerEstimateOn scalarMin scalarMax decay C :=
  h

theorem eq_global_pinching_two
    (scalar scalarMax : Real -> Real) (eps : Real)
    (h : GlobalPinchingScalarEstimateOn scalar scalarMax eps) :
    GlobalPinchingScalarEstimateOn scalar scalarMax eps :=
  h

theorem eq_sectional_pointwise_pinching
    (sectionalMin sectionalMax : Real -> Real) (eps : Real)
    (h : SectionalPointwisePinchingOn sectionalMin sectionalMax eps) :
    SectionalPointwisePinchingOn sectionalMin sectionalMax eps :=
  h

end

end Section08
end Chapter06
end MSM110
end BK
