import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.Geometry


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

/-!
# Perelman F Formula 5.10 Core

Split-out component of the Perelman `F`-functional layer
(`DifferentialGeometry.PDE.RicciFlow.Entropy.F`).
-/

section Formula510

variable {Idx : Type*} [Fintype Idx]

/-- Arbitrary metric-variation Christoffel formula in a fixed frame:
`delta Gamma^k_ij = 1/2 g^{kl}(nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`. -/
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

/-- Trace of the arbitrary metric-variation Christoffel formula:
`delta Gamma^p_pj = 1/2 nabla_j V`. -/
def MetricVariationChristoffelTraceInFrame
    (christoffelTraceVariation metricVariationTraceGradient :
      M -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ j : Idx,
    christoffelTraceVariation x j =
      (1 / 2 : Real) * metricVariationTraceGradient x j

/-- Ricci variation by differentiating the Christoffel variation:
`delta Ric_ij = nabla_p(delta Gamma^p_ij) - nabla_i(delta Gamma^p_pj)`. -/
def RicciVariationByChristoffelInFrame
    (ricciVariation : M -> Idx -> Idx -> Real)
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelTraceVariation : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    ricciVariation x i j =
      (∑ p : Idx, nablaChristoffelVariation x p p i j) -
        nablaChristoffelTraceVariation x i j

/-- Hessian variation for a scalar potential:
`delta Hess_ij f = Hess_ij h - (delta Gamma^p_ij) nabla_p f`. -/
def HessianPotentialVariationByChristoffelInFrame
    (hessianPotentialVariation hessianPotentialVariationDirection :
      M -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    hessianPotentialVariation x i j =
      hessianPotentialVariationDirection x i j -
        ∑ p : Idx, christoffelVariation x p i j * gradPotential x p

/-- Combined variation of `Ric_ij + Hess_ij f` in the weighted-divergence
form used in the book proof. -/
def RicciHessianVariationWeightedDivergenceInFrame
    (ricciHessianVariation weightedDivergenceTerm shiftedHessianTerm :
      M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    ricciHessianVariation x i j =
      weightedDivergenceTerm x i j + shiftedHessianTerm x i j

/-- Sum of Ricci and Hessian variations in a fixed frame. -/
def ricciHessianVariationInFrame
    (ricciVariation hessianVariation : M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j => ricciVariation x i j + hessianVariation x i j

/-- Coordinate expression for
`e^f nabla_p(e^{-f} A^p_ij) = nabla_p A^p_ij - A^p_ij partial_p f`. -/
def christoffelWeightedDivergenceInFrame
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j =>
    (∑ p : Idx, nablaChristoffelVariation x p p i j) -
      ∑ p : Idx, christoffelVariation x p i j * gradPotential x p

/-- Shifted Hessian term `Hess h - Hess(V/2)` in formula 5.10. -/
def shiftedHessianInFrame
    (hessianPotentialVariationDirection metricTraceHessianHalf :
      M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j =>
    hessianPotentialVariationDirection x i j -
      metricTraceHessianHalf x i j

/-- Pointwise assembly of the already separated Ricci and Hessian variation
formulas into the weighted-divergence form used before contraction. -/
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

/-- Variation of `(Ric_ij + Hess_ij f)e^{-f}dmu` before contraction. -/
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

/-- The density-weighted divergence term
`nabla_p(e^{-f} A^p_ij)` when
`weightedDivergenceTerm = e^f nabla_p(e^{-f} A^p_ij)`. -/
def densityWeightedDivergenceInFrame
    (density : M -> Real) (weightedDivergenceTerm : M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j => density x * weightedDivergenceTerm x i j

omit [Fintype Idx] in
/-- Pointwise density variation bridge for
`(Ric_ij + Hess_ij f)e^{-f} dmu`. -/
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

/-- Frame contraction of a metric variation against `Ric + Hess f`. -/
def metricVariationRicciHessContractInFrame
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) : M -> Real :=
  fun x =>
    ∑ i : Idx, ∑ j : Idx,
      metricVariation x i j * ricciHessian x i j

/-- Inverse-metric variation contribution in formula 5.10:
`delta g^{ij}(Ric_ij + Hess_ij f) = -v_ij(Ric_ij + Hess_ij f)`. -/
def inverseMetricVariationContractionTermInFrame
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) : M -> Real :=
  fun x => -metricVariationRicciHessContractInFrame metricVariation ricciHessian x

/-- Public bridge naming the inverse-metric contraction contribution. -/
theorem inverseMetricVariationContractionTerm_eq_neg
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) :
    inverseMetricVariationContractionTermInFrame metricVariation ricciHessian =
      fun x => -metricVariationRicciHessContractInFrame metricVariation
        ricciHessian x := rfl

end Formula510

/-- Final weighted-measure integrand in MSM135 formula 5.10. -/
def fFunctionalFormula510Integrand
    (scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :
      M -> Real) :
    M -> Real :=
  fun x =>
    -metricVariationRicciHess x +
      (metricVariationTrace x / 2 - potentialVariation x) *
        (2 * lapPotential x - gradPotentialNormSq x + scalarCurvature x)

/-- Formula 5.10 as a final integral identity. -/
def FFunctionalFormula510 [MeasurableSpace M] (weightedMeasure : Measure M)
    (firstVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess : M -> Real) : Prop :=
  firstVariation =
    ∫ x,
      fFunctionalFormula510Integrand scalarCurvature lapPotential
        gradPotentialNormSq potentialVariation metricVariationTrace
        metricVariationRicciHess x
      ∂weightedMeasure

/-- Pre-cancellation scalar integrand for the closed-manifold formula 5.10
assembly.  It is the contracted first-variation integrand before the closed
weighted-divergence term and weighted Green term are canceled. -/
def fFunctionalPre510Integrand
    (scalarCurvature lapPotential _gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    M -> Real :=
  fun x =>
    -metricVariationRicciHess x +
      weightedDivergenceTrace x + shiftedTrace x +
        (scalarCurvature x + lapPotential x) *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x

/-- The remainder canceled by closed divergence plus weighted Green in formula
5.10. -/
def fFunctional510Remainder
    (lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    M -> Real :=
  fun x =>
    weightedDivergenceTrace x +
      (shiftedTrace x -
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (lapPotential x - gradPotentialNormSq x))

/-- Pointwise scalar algebra behind formula 5.10 after the geometric producers
have produced the pre-cancellation integrand. -/
theorem pre510_eq_final_add_rem
    (scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    fFunctionalPre510Integrand scalarCurvature lapPotential
        gradPotentialNormSq potentialVariation metricVariationTrace
        metricVariationRicciHess weightedDivergenceTrace shiftedTrace =
      fun x : M =>
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x +
        fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x := by
  funext x
  unfold fFunctionalPre510Integrand fFunctionalFormula510Integrand
    fFunctional510Remainder expWeightedMeasureVariationFactor
  ring

/-- Pointwise bridge from the moving-volume derivative integrand to the
pre-cancellation formula 5.10 integrand.

The hypothesis is exactly the geometric variation of `R + |grad f|^2` before
closed weighted Green cancels the shifted trace. -/
theorem expWeightedIntegralVariation_eq_pre510
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
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x := by
  intro x
  unfold expWeightedIntegralVariationIntegrand fFunctionalPre510Integrand
    fFunctionalBracket
  rw [hvariation x]
  unfold expWeightedMeasureVariationFactor
  ring

/-- Pointwise closed-bracket version of the formula 5.10 integrand bridge.
Here the geometric producer differentiates the closed bracket `R + Delta f`,
so the extra `(Delta f - |grad f|^2)` correction is supplied by the later
integral comparison with the original `R + |grad f|^2` bracket. -/
theorem expWeightedClosedVariation_eq_pre510
    {scalarCurvature lapPotential gradPotentialNormSq potential
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
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x := by
  intro x
  unfold expWeightedIntegralVariationIntegrand fFunctionalPre510Integrand
    fFunctionalClosedBracket
  rw [hvariation x]

/-- The formula 5.10 remainder has zero integral once the closed divergence
term vanishes and weighted Green identifies the shifted Hessian trace. -/
theorem rem510_integral_zero [MeasurableSpace M]
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
      fFunctional510Remainder lapPotential gradPotentialNormSq
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
  unfold fFunctional510Remainder
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

/-- Formula 5.10 from the pre-cancellation scalar integrand and a zero
remainder. -/
theorem formula510_of_rem_zero [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess weightedDivergenceTrace
      shiftedTrace : M -> Real}
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂weightedMeasure)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        weightedMeasure)
    (hrem_int :
      Integrable
        (fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace)
        weightedMeasure)
    (hrem_zero :
      ∫ x,
        fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x
        ∂weightedMeasure = 0) :
    FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  unfold FFunctionalFormula510
  rw [hfirst]
  calc
    ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂weightedMeasure =
      ∫ x,
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess x +
          fFunctional510Remainder lapPotential gradPotentialNormSq
            potentialVariation metricVariationTrace weightedDivergenceTrace
            shiftedTrace x)
        ∂weightedMeasure := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [pre510_eq_final_add_rem]
    _ =
      ∫ x,
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure +
      ∫ x,
        fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x
        ∂weightedMeasure := by
      rw [integral_add hfinal_int hrem_int]
    _ =
      ∫ x,
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure := by
      rw [hrem_zero, add_zero]

/-- Formula 5.10 from the closed divergence cancellation and weighted Green
identification of the shifted Hessian trace. -/
theorem formula510_of_ints [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess weightedDivergenceTrace
      shiftedTrace : M -> Real}
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂weightedMeasure)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
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
    FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  apply formula510_of_rem_zero
    (weightedDivergenceTrace := weightedDivergenceTrace)
    (shiftedTrace := shiftedTrace)
    hfirst hfinal_int
  · unfold fFunctional510Remainder
    exact hdiv_int.add (hshift_int.sub hcorr_int)
  · exact rem510_integral_zero hdiv_int hshift_int hcorr_int
      hdiv_zero hshift


end

end DifferentialGeometry.PDE.RicciFlow.Entropy
