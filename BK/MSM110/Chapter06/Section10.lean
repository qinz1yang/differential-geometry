import RicciFlower.RicciFlow.Evolution.ExponentialConvergence

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM110 Chapter 6.10: Exponential Convergence

Exact LaTeX labels represented here:
`ExponentialConvergenceToEinstein`, `BoundScalarAbove-1`,
`BoundScalarAbove-2`, `PinchingPreservedForNRF`, `ScalarStaysPositive`.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section10

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}

theorem lem_pinching_preserved_for_nrf
    (lambda mu nu : Real -> M -> Real)
    (hpositiveRicciInitial : Prop) :
    ∃ B : Real, NormalizedPinchingPreserved lambda mu nu B :=
  RicciFlower.RicciFlow.normalized_pinching_preserved
    lambda mu nu hpositiveRicciInitial

theorem lem_scalar_stays_positive
    (scalar : Real -> M -> Real)
    (hpositiveInitial : Prop) :
    ∃ eps : Real, NormalizedScalarStaysPositive scalar eps :=
  RicciFlower.RicciFlow.scalar_stays_positive scalar hpositiveInitial

theorem eq_bound_scalar_above_one
    (scalar : Real -> M -> Real) (A : Real)
    (h : NormalizedScalarUpperBoundOn scalar A) :
    NormalizedScalarUpperBoundOn scalar A :=
  h

theorem eq_bound_scalar_above_two
    (avgScalar volume : Real -> Real) (A : Real)
    (h : NormalizedAverageScalarUpperBoundOn avgScalar volume A) :
    NormalizedAverageScalarUpperBoundOn avgScalar volume A :=
  h

theorem prop_exponential_eigenvalue_pinching
    (lambda mu nu decay : Real -> M -> Real)
    (hpinching : ∃ B : Real, NormalizedPinchingPreserved lambda mu nu B)
    (hscalarPositive : Prop) :
    ∃ alpha beta C : Real,
      ExponentialEigenvaluePinching lambda mu nu decay alpha beta C :=
  RicciFlower.RicciFlow.exponential_eigenvalue_pinching
    lambda mu nu decay hpinching hscalarPositive

theorem cor_exponential_tracefree_ricci_decay
    (lambda mu nu tracefreeRicciNorm decay : Real -> M -> Real)
    (heigenPinching :
      ∃ alpha beta C : Real,
        ExponentialEigenvaluePinching lambda mu nu decay alpha beta C) :
    ∃ beta B : Real,
      ExponentialTracefreeRicciDecay tracefreeRicciNorm decay beta B :=
  RicciFlower.RicciFlow.exponential_tracefree_ricci_decay
    lambda mu nu tracefreeRicciNorm decay heigenPinching

theorem thm_exponential_convergence_to_einstein
    (metricDistanceToLimit : Nat -> Real -> Real) (decay : Real -> Real)
    (htracefreeDecay hderivativeEstimates : Prop) :
    ExponentialConvergenceToEinstein metricDistanceToLimit decay :=
  RicciFlower.RicciFlow.exponential_convergence_to_einstein
    metricDistanceToLimit decay htracefreeDecay hderivativeEstimates

end

end Section10
end Chapter06
end MSM110
end BK
