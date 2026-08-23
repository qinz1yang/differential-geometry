import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.GeometricFirstVariation

set_option autoImplicit false

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

theorem fFunctionalFirstVariationFormula_of_pointwise_identity [MeasurableSpace M]
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
          fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess x) :
    FFunctionalFirstVariationFormula weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  unfold FFunctionalFirstVariationFormula
  rw [hfirst]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hpoint

theorem fFunctionalFirstVariation_eq_integral_of_formula
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
      FFunctionalFirstVariationFormula weightedMeasure firstVariation scalarCurvature
        lapPotential gradPotentialNormSq potentialVariation
        metricVariationTrace metricVariationRicciHess) :
    fFunctionalFirstVariation muPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 =
      ∫ x,
        fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure := by
  rw [fFunctionalFirstVariation_eq_of_hasFirstVariationAt hderiv]
  exact hformula

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
