import RicciFlower.RicciFlow.Perelman.F.Producer


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace RicciFlow
namespace Perelman

noncomputable section

open Filter MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open RicciFlower.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

/-!
# Perelman F Final Wrappers

Split-out component of `RicciFlow.Perelman.F`.
-/

/-- Final assembly adapter for formula 5.10 once the previous producer chain has
identified the first-variation integrand pointwise. -/
theorem formula510_of_steps [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {preIntegrand scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :
      M -> Real}
    (hfirst :
      firstVariation = ∫ x, preIntegrand x ∂weightedMeasure)
    (hpoint :
      ∀ x : M,
        preIntegrand x =
          fFunctionalFormula510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess x) :
    FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  unfold FFunctionalFormula510
  rw [hfirst]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hpoint

/-- If formula 5.10 has been proved for the first variation value, then the
`deriv`-based first variation agrees with the formula 5.10 integral. -/
theorem fFunctionalFirstVariation_eq_formula510_of_hasFirstVariationAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {weightedMeasure : Measure M} {s0 firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess : M -> Real}
    (hderiv :
      FFunctionalHasFirstVariationAt muPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 firstVariation)
    (hformula :
      FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
        lapPotential gradPotentialNormSq potentialVariation
        metricVariationTrace metricVariationRicciHess) :
    fFunctionalFirstVariation muPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 =
      ∫ x,
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure := by
  rw [fFunctionalFirstVariation_eq_of_hasFirstVariationAt hderiv]
  exact hformula

end

end Perelman
end RicciFlow
end RicciFlower
