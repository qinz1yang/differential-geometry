import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.Geometry
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

section FirstVariationFormula

variable {Idx : Type*} [Fintype Idx]

def MetricVariationChristoffelInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (nablaMetricVariation christoffelVariation :
      M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j k : Idx,
    christoffelVariation x k i j =
      (1 / 2 : Real) *
        ∑ l : Idx, gInv x k l *
          (nablaMetricVariation x i j l +
            nablaMetricVariation x j i l -
              nablaMetricVariation x l i j)

def MetricVariationChristoffelTraceInFrame
    (christoffelTraceVariation metricVariationTraceGradient :
      M -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ j : Idx,
    christoffelTraceVariation x j =
      (1 / 2 : Real) * metricVariationTraceGradient x j

def RicciVariationByChristoffelInFrame
    (ricciVariation : M -> Idx -> Idx -> Real)
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelTraceVariation : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    ricciVariation x i j =
      (∑ p : Idx, nablaChristoffelVariation x p p i j) -
        nablaChristoffelTraceVariation x i j

def HessianPotentialVariationByChristoffelInFrame
    (hessianPotentialVariation hessianPotentialVariationDirection :
      M -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    hessianPotentialVariation x i j =
      hessianPotentialVariationDirection x i j -
        ∑ p : Idx, christoffelVariation x p i j * gradPotential x p

def RicciHessianVariationWeightedDivergenceInFrame
    (ricciHessianVariation weightedDivergenceTerm shiftedHessianTerm :
      M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    ricciHessianVariation x i j =
      weightedDivergenceTerm x i j + shiftedHessianTerm x i j

def ricciHessianVariationInFrame
    (ricciVariation hessianVariation : M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j => ricciVariation x i j + hessianVariation x i j

def christoffelWeightedDivergenceInFrame
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j =>
    (∑ p : Idx, nablaChristoffelVariation x p p i j) -
      ∑ p : Idx, christoffelVariation x p i j * gradPotential x p

def shiftedHessianInFrame
    (hessianPotentialVariationDirection metricTraceHessianHalf :
      M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j =>
    hessianPotentialVariationDirection x i j -
      metricTraceHessianHalf x i j

theorem ricciHessianWeightedDivergence_of_ricci_hessian
    (ricciVariation hessianVariation hessianPotentialVariationDirection :
      M -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelTraceVariation metricTraceHessianHalf :
      M -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real)
    (hRic :
      RicciVariationByChristoffelInFrame ricciVariation
        nablaChristoffelVariation nablaChristoffelTraceVariation)
    (hHess :
      HessianPotentialVariationByChristoffelInFrame hessianVariation
        hessianPotentialVariationDirection christoffelVariation gradPotential)
    (hTrace :
      ∀ x : M, ∀ i j : Idx,
        nablaChristoffelTraceVariation x i j =
          metricTraceHessianHalf x i j) :
    RicciHessianVariationWeightedDivergenceInFrame
      (ricciHessianVariationInFrame ricciVariation hessianVariation)
      (christoffelWeightedDivergenceInFrame nablaChristoffelVariation
        christoffelVariation gradPotential)
      (shiftedHessianInFrame hessianPotentialVariationDirection
        metricTraceHessianHalf) := by
  intro x i j
  rw [ricciHessianVariationInFrame, hRic x i j, hHess x i j, hTrace x i j]
  simp [christoffelWeightedDivergenceInFrame, shiftedHessianInFrame,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

def RicciHessianWeightedDensityVariationInFrame
    (weightedVariation weightedDivergenceTerm shiftedHessianTerm
      ricciHessian : M -> Idx -> Idx -> Real)
    (potentialVariation metricVariationTrace density : M -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    weightedVariation x i j =
      weightedDivergenceTerm x i j +
        density x * shiftedHessianTerm x i j +
          ricciHessian x i j * density x *
            expWeightedMeasureVariationFactor potentialVariation
              metricVariationTrace x

def densityWeightedDivergenceInFrame
    (density : M -> Real) (weightedDivergenceTerm : M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j => density x * weightedDivergenceTerm x i j

omit [Fintype Idx] in
theorem ricciHessianWeightedDensity_of_divergence
    (weightedDivergenceTerm shiftedHessianTerm ricciHessian :
      M -> Idx -> Idx -> Real)
    (density potentialVariation metricVariationTrace : M -> Real) :
    RicciHessianWeightedDensityVariationInFrame
      (fun x i j =>
        densityWeightedDivergenceInFrame density weightedDivergenceTerm x i j +
          density x * shiftedHessianTerm x i j +
            ricciHessian x i j * density x *
              expWeightedMeasureVariationFactor potentialVariation
                metricVariationTrace x)
      (densityWeightedDivergenceInFrame density weightedDivergenceTerm)
      shiftedHessianTerm ricciHessian potentialVariation metricVariationTrace
      density := by
  intro x i j
  rfl

def metricVariationRicciHessContractInFrame
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) : M -> Real :=
  fun x =>
    ∑ i : Idx, ∑ j : Idx,
      metricVariation x i j * ricciHessian x i j

def inverseMetricVariationContractionTermInFrame
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) : M -> Real :=
  fun x => -metricVariationRicciHessContractInFrame metricVariation ricciHessian x

theorem inverseMetricVariationContractionTerm_eq_neg
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) :
    inverseMetricVariationContractionTermInFrame metricVariation ricciHessian =
      fun x => -metricVariationRicciHessContractInFrame metricVariation
        ricciHessian x := rfl

end FirstVariationFormula

def fFunctionalFirstVariationIntegrand
    (scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :
      M -> Real) :
    M -> Real :=
  fun x =>
    -metricVariationRicciHess x +
      (metricVariationTrace x / 2 - potentialVariation x) *
        (2 * lapPotential x - gradPotentialNormSq x + scalarCurvature x)

def FFunctionalFirstVariationFormula [MeasurableSpace M] (weightedMeasure : Measure M)
    (firstVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess : M -> Real) : Prop :=
  firstVariation =
    ∫ x,
      fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
        gradPotentialNormSq potentialVariation metricVariationTrace
        metricVariationRicciHess x
      ∂weightedMeasure

def fFunctionalPreIntegrationByPartsIntegrand
    (scalarCurvature lapPotential potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    M -> Real :=
  fun x =>
    -metricVariationRicciHess x +
      weightedDivergenceTrace x + shiftedTrace x +
        (scalarCurvature x + lapPotential x) *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x

def fFunctionalIntegrationByPartsRemainder
    (lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    M -> Real :=
  fun x =>
    weightedDivergenceTrace x +
      (shiftedTrace x -
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (lapPotential x - gradPotentialNormSq x))

theorem fFunctionalPreIntegrationByPartsIntegrand_eq_firstVariationIntegrand_add_remainder
    (scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    fFunctionalPreIntegrationByPartsIntegrand scalarCurvature lapPotential potentialVariation metricVariationTrace
        metricVariationRicciHess weightedDivergenceTrace shiftedTrace =
      fun x : M =>
        fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x +
        fFunctionalIntegrationByPartsRemainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x := by
  funext x
  unfold fFunctionalPreIntegrationByPartsIntegrand fFunctionalFirstVariationIntegrand
    fFunctionalIntegrationByPartsRemainder expWeightedMeasureVariationFactor
  ring

theorem expWeightedIntegralVariationIntegrand_eq_preIntegrationByParts
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      gradPotentialNormSqVariation : M -> Real}
    (hvariation :
      ∀ x : M,
        fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x +
            (lapPotential x - gradPotentialNormSq x) *
              expWeightedMeasureVariationFactor potentialVariation
                metricVariationTrace x) :
    ∀ x : M,
      expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalBracket scalarCurvature gradPotentialNormSq)
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x =
      expNegPotentialDensity potential x *
          fFunctionalPreIntegrationByPartsIntegrand scalarCurvature lapPotential potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x := by
  intro x
  unfold expWeightedIntegralVariationIntegrand fFunctionalPreIntegrationByPartsIntegrand
    fFunctionalBracket
  rw [hvariation x]
  unfold expWeightedMeasureVariationFactor
  ring

theorem expWeightedClosedVariationIntegrand_eq_preIntegrationByParts
    {scalarCurvature lapPotential potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace closedBracketVariation :
      M -> Real}
    (hvariation :
      ∀ x : M,
        closedBracketVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    ∀ x : M,
      expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x =
      expNegPotentialDensity potential x *
          fFunctionalPreIntegrationByPartsIntegrand scalarCurvature lapPotential potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x := by
  intro x
  unfold expWeightedIntegralVariationIntegrand fFunctionalPreIntegrationByPartsIntegrand
    fFunctionalClosedBracket
  rw [hvariation x]

theorem fFunctionalIntegrationByPartsRemainder_integral_eq_zero [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      weightedDivergenceTrace shiftedTrace : M -> Real}
    (hdiv_int : Integrable weightedDivergenceTrace weightedMeasure)
    (hshift_int : Integrable shiftedTrace weightedMeasure)
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hdiv_zero :
      ∫ x, weightedDivergenceTrace x ∂weightedMeasure = 0)
    (hshift :
      ∫ x, shiftedTrace x ∂weightedMeasure =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
          ∂weightedMeasure) :
    ∫ x,
      fFunctionalIntegrationByPartsRemainder lapPotential gradPotentialNormSq
        potentialVariation metricVariationTrace weightedDivergenceTrace
        shiftedTrace x
      ∂weightedMeasure = 0 := by
  let corr : M -> Real := fun x =>
    expWeightedMeasureVariationFactor potentialVariation
      metricVariationTrace x *
      (lapPotential x - gradPotentialNormSq x)
  have hcorr_int' : Integrable corr weightedMeasure := by
    simpa [corr] using hcorr_int
  have hshift' :
      ∫ x, shiftedTrace x ∂weightedMeasure =
        ∫ x, corr x ∂weightedMeasure := by
    simpa [corr] using hshift
  unfold fFunctionalIntegrationByPartsRemainder
  change
    ∫ x, weightedDivergenceTrace x + (shiftedTrace - corr) x
      ∂weightedMeasure = 0
  rw [integral_add hdiv_int (hshift_int.sub hcorr_int')]
  change
    ∫ x, weightedDivergenceTrace x ∂weightedMeasure +
      ∫ x, shiftedTrace x - corr x ∂weightedMeasure = 0
  rw [integral_sub hshift_int hcorr_int']
  rw [hdiv_zero, hshift']
  ring

theorem fFunctionalFirstVariationFormula_of_remainder_integral_eq_zero [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess weightedDivergenceTrace
      shiftedTrace : M -> Real}
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPreIntegrationByPartsIntegrand scalarCurvature lapPotential potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂weightedMeasure)
    (hfinal_int :
      Integrable
        (fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        weightedMeasure)
    (hrem_int :
      Integrable
        (fFunctionalIntegrationByPartsRemainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace)
        weightedMeasure)
    (hrem_zero :
      ∫ x,
        fFunctionalIntegrationByPartsRemainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x
        ∂weightedMeasure = 0) :
    FFunctionalFirstVariationFormula weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  unfold FFunctionalFirstVariationFormula
  rw [hfirst]
  calc
    ∫ x,
        fFunctionalPreIntegrationByPartsIntegrand scalarCurvature lapPotential potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂weightedMeasure =
      ∫ x,
        (fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess x +
          fFunctionalIntegrationByPartsRemainder lapPotential gradPotentialNormSq
            potentialVariation metricVariationTrace weightedDivergenceTrace
            shiftedTrace x)
        ∂weightedMeasure := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [fFunctionalPreIntegrationByPartsIntegrand_eq_firstVariationIntegrand_add_remainder]
    _ =
      ∫ x,
        fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure +
      ∫ x,
        fFunctionalIntegrationByPartsRemainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x
        ∂weightedMeasure := by
      rw [integral_add hfinal_int hrem_int]
    _ =
      ∫ x,
        fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure := by
      rw [hrem_zero, add_zero]

theorem fFunctionalFirstVariationFormula_of_integration_by_parts [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess weightedDivergenceTrace
      shiftedTrace : M -> Real}
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPreIntegrationByPartsIntegrand scalarCurvature lapPotential potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂weightedMeasure)
    (hfinal_int :
      Integrable
        (fFunctionalFirstVariationIntegrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        weightedMeasure)
    (hdiv_int : Integrable weightedDivergenceTrace weightedMeasure)
    (hshift_int : Integrable shiftedTrace weightedMeasure)
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hdiv_zero :
      ∫ x, weightedDivergenceTrace x ∂weightedMeasure = 0)
    (hshift :
      ∫ x, shiftedTrace x ∂weightedMeasure =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
          ∂weightedMeasure) :
    FFunctionalFirstVariationFormula weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  apply fFunctionalFirstVariationFormula_of_remainder_integral_eq_zero
    (weightedDivergenceTrace := weightedDivergenceTrace)
    (shiftedTrace := shiftedTrace)
    hfirst hfinal_int
  · unfold fFunctionalIntegrationByPartsRemainder
    exact hdiv_int.add (hshift_int.sub hcorr_int)
  · exact fFunctionalIntegrationByPartsRemainder_integral_eq_zero hdiv_int hshift_int hcorr_int
      hdiv_zero hshift

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
