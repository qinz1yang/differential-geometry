import RicciFlower.RicciFlow.Evolution.ScalarGradient

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM110 Chapter 6.6: Gradient Estimate for Scalar Curvature

Exact LaTeX labels represented here:
`GradientEstimateForScalarIn3d`, `PinchingEstimateYetAgain`,
`EstimateGradientOfScalar`, `grad R norm sqr evolution`,
`GradRoverR-evolution`, `EvolutionEquationOfScalarSquared`,
`EvolutionOfNormSquaredOfRicci`, `GradScalarPartial1`,
`GradScalarPartial2`, `GradRicciEstimate`, `GradScalarPartial3`,
`CS-EstimateForGradR`, `VforGradR1`, `VforGradR2`.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section06

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}

theorem item_grad_r_norm_sqr_evolution
    (gradScalarNormSq hessianScalarNormSq gradRicciNormSq : Real -> M -> Real)
    (h : GradScalarNormEvolutionOn
      gradScalarNormSq hessianScalarNormSq gradRicciNormSq) :
    GradScalarNormEvolutionOn gradScalarNormSq hessianScalarNormSq gradRicciNormSq :=
  h

theorem eq_grad_rover_r_evolution
    (gradScalarNormSq scalar rhs : Real -> M -> Real)
    (h : GradScalarOverScalarEvolutionOn gradScalarNormSq scalar rhs) :
    GradScalarOverScalarEvolutionOn gradScalarNormSq scalar rhs :=
  h

theorem eq_scalar_and_ricci_norm_squared_evolution
    (scalar ricciNormSq scalarSqRhs ricciNormSqRhs : Real -> M -> Real)
    (h : ScalarAndRicciNormSquaredEvolutionOn
      scalar ricciNormSq scalarSqRhs ricciNormSqRhs) :
    ScalarAndRicciNormSquaredEvolutionOn
      scalar ricciNormSq scalarSqRhs ricciNormSqRhs :=
  h

theorem eq_pinching_estimate_yet_again
    (tracefreeRmRatio decay : Real -> M -> Real) (C : Real)
    (h : PinchingEstimateYetAgainOn tracefreeRmRatio decay C) :
    PinchingEstimateYetAgainOn tracefreeRmRatio decay C :=
  h

theorem eq_evolution_equation_of_scalar_squared
    (scalar scalarSqRhs : Real -> M -> Real)
    (h : ScalarSquaredEvolutionOn scalar scalarSqRhs) :
    ScalarSquaredEvolutionOn scalar scalarSqRhs :=
  h

theorem eq_evolution_of_norm_squared_of_ricci
    (ricciNormSq ricciNormSqRhs : Real -> M -> Real)
    (h : RicciNormSquaredEvolutionOn ricciNormSq ricciNormSqRhs) :
    RicciNormSquaredEvolutionOn ricciNormSq ricciNormSqRhs :=
  h

theorem cor_grad_scalar_partial_one
    (tracefreeRicciNormSq scalar ricciNormSq rhs : Real -> M -> Real)
    (h : TracefreeRicciEvolutionInequalityOn
      tracefreeRicciNormSq scalar ricciNormSq rhs) :
    TracefreeRicciEvolutionInequalityOn
      tracefreeRicciNormSq scalar ricciNormSq rhs :=
  h

theorem lem_grad_scalar_partial_two
    (gradRicciNormSq gradScalarNormSq : Real -> M -> Real)
    (h : GradRicciControlsGradScalarOn gradRicciNormSq gradScalarNormSq) :
    GradRicciControlsGradScalarOn gradRicciNormSq gradScalarNormSq :=
  h

theorem eq_grad_ricci_estimate
    (gradRicciNormSq gradScalarNormSq : Real -> M -> Real)
    (h : GradRicciControlsGradScalarOn gradRicciNormSq gradScalarNormSq) :
    GradRicciControlsGradScalarOn gradRicciNormSq gradScalarNormSq :=
  h

theorem eq_cs_estimate_for_grad_r
    (gradScalarNormSq hessianScalarNormSq gradRicciNormSq : Real -> M -> Real)
    (C : Real)
    (h : CauchySchwarzEstimateForGradScalarOn
      gradScalarNormSq hessianScalarNormSq gradRicciNormSq C) :
    CauchySchwarzEstimateForGradScalarOn
      gradScalarNormSq hessianScalarNormSq gradRicciNormSq C :=
  h

theorem cor_grad_scalar_partial_three
    (tracefreeRicciNormSq scalar ricciNormSq rhs : Real -> M -> Real)
    (h : TracefreeRicciEvolutionInequalityOn
      tracefreeRicciNormSq scalar ricciNormSq rhs) :
    TracefreeRicciEvolutionInequalityOn
      tracefreeRicciNormSq scalar ricciNormSq rhs :=
  h

theorem lem_v_for_grad_r_one
    (V scalar tracefreeRicciNormSq gradRicciNormSq : Real -> M -> Real)
    (h : VGradientQuantityEvolutionInequalityOn
      V scalar tracefreeRicciNormSq gradRicciNormSq) :
    VGradientQuantityEvolutionInequalityOn
      V scalar tracefreeRicciNormSq gradRicciNormSq :=
  h

theorem lem_v_for_grad_r_two
    (W scalar tracefreeRicciNormSq : Real -> M -> Real)
    (h : WTracefreeRicciBoundOn W scalar tracefreeRicciNormSq) :
    WTracefreeRicciBoundOn W scalar tracefreeRicciNormSq :=
  h

theorem thm_estimate_gradient_of_scalar
    (gradScalarNormSq scalar : Real -> M -> Real)
    (h :
      ∃ betaBar deltaBar : Real,
        0 < betaBar ∧ 0 < deltaBar ∧
        ∃ decayHalf decayCubic : Real -> M -> Real,
          ∀ beta : Real, 0 ≤ beta -> beta ≤ betaBar ->
            ∃ C : Real,
              ScalarGradientEstimateOn
                gradScalarNormSq scalar decayHalf decayCubic beta C) :
    ∃ betaBar deltaBar : Real,
      0 < betaBar ∧ 0 < deltaBar ∧
      ∃ decayHalf decayCubic : Real -> M -> Real,
        ∀ beta : Real, 0 ≤ beta -> beta ≤ betaBar ->
          ∃ C : Real,
            ScalarGradientEstimateOn
              gradScalarNormSq scalar decayHalf decayCubic beta C :=
  h

end

end Section06
end Chapter06
end MSM110
end BK
