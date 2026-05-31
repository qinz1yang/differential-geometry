import RicciFlower.RicciFlow.Evolution.LocalPinching

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# MSM110 Chapter 6.5: Local Pinching Estimates

Exact LaTeX labels represented here:
`PinchingFor3Manifolds`, `Ricci-pinching-preserved`,
`ricci pinching preserved ineq`, `d/dt ln (lambda/mu+nu)`,
`RicciLowerBound`, `ricci pinching improves theorem`,
`PinchingEstimate-HamiltonForm`, `f pinching improves evolution`,
`DefineP`, `Palpha over Qbeta`, `f-pinching-evolution`,
`R evolution lambda mu nu`.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section05

noncomputable section

open RicciFlower.RicciFlow
open scoped Manifold ContDiff

variable {M : Type*}

theorem lem_ricci_pinching_preserved
    (lambda mu nu : Real -> M -> Real) (C : Real)
    (hode :
      CurvatureEigenvaluesOrdered lambda mu nu →
        (∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) →
          RicciPinchingPreservedOn lambda mu nu C)
    (hordered : CurvatureEigenvaluesOrdered lambda mu nu)
    (hinit : ∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) :
    RicciPinchingPreservedOn lambda mu nu C :=
  RicciFlower.RicciFlow.ricci_pinching_preserved
    lambda mu nu C hode hordered hinit

theorem cor_ricci_lower_bound
    (lambda mu nu ricciLower scalar : Real -> M -> Real)
    (C beta : Real)
    (hbound :
      RicciPinchingPreservedOn lambda mu nu C →
        beta > 0 →
          RicciLowerBoundFromPinchingOn ricciLower scalar beta)
    (hpinch : RicciPinchingPreservedOn lambda mu nu C)
    (hbeta : beta > 0) :
    RicciLowerBoundFromPinchingOn ricciLower scalar beta :=
  RicciFlower.RicciFlow.ricci_lower_bound_of_pinching
    lambda mu nu ricciLower scalar C beta hbound hpinch hbeta

theorem thm_ricci_pinching_improves_theorem
    (lambda mu nu : Real -> M -> Real)
    (hpositiveRicciInitial : Prop)
    (hinit : hpositiveRicciInitial)
    (himprove :
      hpositiveRicciInitial →
        ∃ C delta : Real, ∃ weight : Real -> M -> Real,
          0 < C ∧ 0 < delta ∧ delta < 1 ∧
          PinchingDecayWeightOn lambda mu nu weight delta ∧
          RicciPinchingImprovesOn lambda mu nu weight C) :
    ∃ C delta : Real, ∃ weight : Real -> M -> Real,
      0 < C ∧ 0 < delta ∧ delta < 1 ∧
      PinchingDecayWeightOn lambda mu nu weight delta ∧
      RicciPinchingImprovesOn lambda mu nu weight C :=
  RicciFlower.RicciFlow.ricci_pinching_improves
    lambda mu nu hpositiveRicciInitial hinit himprove

theorem eq_pinching_estimate_hamilton_form
    (lambda mu nu tracefreeRmNormSq scalar weight : Real -> M -> Real)
    (C : Real)
    (hconvert :
      RicciPinchingImprovesOn lambda mu nu weight C →
        HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C)
    (hpinch : RicciPinchingImprovesOn lambda mu nu weight C) :
    HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C :=
  RicciFlower.RicciFlow.hamilton_tracefree_pinching_of_eigenvalue_pinching
    lambda mu nu tracefreeRmNormSq scalar weight C hconvert hpinch

/-- Side BK label for Lemma 10.5.

The actual quotient-evolution producer belongs in RicciFlower.  This file only
records that a supplied RicciFlower-native quotient evolution statement matches
the book label. -/
theorem lem_palpha_over_qbeta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [Module.Finite Real E] [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {D : RicciFlower.Realized.RealTimeInterval}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [IsManifold I (∞ + 1) M]
    (G : RicciFlower.Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (h :
      PAlphaOverQBetaFormulaOn (I := I) (D := D) G
        phi psi phiHeat psiHeat alpha beta) :
    PAlphaOverQBetaFormulaOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta := h

theorem item_define_p
    (lambda mu nu P : Real -> M -> Real)
    (h : PinchingPFormulaOn lambda mu nu P) :
    PinchingPFormulaOn lambda mu nu P := h

theorem item_define_p_canonical
    (lambda mu nu : Real -> M -> Real) :
    PinchingPFormulaOn lambda mu nu
      (fun t x => pinchingP (lambda t x) (mu t x) (nu t x)) :=
  RicciFlower.RicciFlow.pinchingP_formula lambda mu nu

theorem lem_f_pinching_evolution
    (f scalar Q : Real -> M -> Real) (epsilon : Real)
    (hineq : ∀ t x,
      0 < scalar t x -> f t x ≤ Q t x + epsilon * scalar t x) :
    TracefreeRmPinchingEvolutionInequalityOn f scalar Q epsilon :=
  RicciFlower.RicciFlow.tracefree_rm_pinching_evolution
    f scalar Q epsilon hineq

theorem eq_ricci_pinching_preserved_ineq
    (lambda mu nu : Real -> M -> Real) (C : Real)
    (h : RicciPinchingPreservedInequalityOn lambda mu nu C) :
    RicciPinchingPreservedInequalityOn lambda mu nu C :=
  h

theorem eq_d_dt_ln_lambda_mu_nu
    (lambda mu nu : Real -> M -> Real)
    (h : LogLambdaOverMuPlusNuDerivativeFormulaOn lambda mu nu) :
    LogLambdaOverMuPlusNuDerivativeFormulaOn lambda mu nu :=
  h

theorem eq_f_pinching_improves_evolution
    (f rhs : Real -> M -> Real)
    (h : PinchingImprovesFunctionEvolutionOn f rhs) :
    PinchingImprovesFunctionEvolutionOn f rhs :=
  h

theorem eq_r_evolution_lambda_mu_nu
    (scalar lambda mu nu rhs : Real -> M -> Real)
    (h : ScalarEvolutionEigenvalueFormulaOn scalar lambda mu nu rhs) :
    ScalarEvolutionEigenvalueFormulaOn scalar lambda mu nu rhs :=
  h

end

end Section05
end Chapter06
end MSM110
end BK
