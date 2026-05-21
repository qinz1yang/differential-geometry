import RicciFlower.RicciFlow.Perelman.FirstVariation

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.1: W entropy and monotonicity

Book-facing wrappers for labels `lbl542`-`lbl599`.  The proofs here are only
aliases to the RicciFlower Perelman statement predicates.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section01

noncomputable section

open MeasureTheory
open RicciFlower.RicciFlow.Perelman

variable {M : Type*}

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl543` and
`notes_and_commentary:lbl545`. -/
theorem lbl543_density_normalization {n : Nat} {S : WeightedEntropyState M}
    (h : PositiveNormalizedDensity n S) :
    PositiveNormalizedDensity n S := h

/-- MSM135 Chapter 6, label `notes_and_commentary:lbl544`. -/
theorem lbl544_w_entropy_formula {n : Nat} {S : WeightedEntropyState M}
    {integral value : Real}
    (h : WEntropyFormula n S integral value) :
    WEntropyFormula n S integral value := h

/-- MSM135 Chapter 6.1, concrete version of label
`notes_and_commentary:lbl544`.

This is the formalized integral
`W = integral_M [tau * (R + |grad f|^2) + f - n] u dmu`, where the weighted
measure is `u dmu` and `u = (4*pi*tau)^(-n/2) * exp (-f)`. -/
theorem lbl544_w_functional_eq_integral [MeasurableSpace M] (mu : Measure M)
    (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂(perelmanWeightedMeasure mu n tau potential) :=
  wFunctional_eq_integral mu n tau scalarCurvature gradPotentialNormSq potential

/-- MSM135 Chapter 6.1, label `notes_and_commentary:lbl548`, scale
invariance of `W`.

The wrapper exposes the book property using the exact scaling laws still needed
from the metric layer: the weighted measures agree, scalar curvature scales by
`c`, and the gradient-square term scales by `c`. -/
theorem lbl548_w_entropy_scale_invariance [MeasurableSpace M]
    {mu scaledMu : Measure M} {n : Nat} {tau c : Real}
    {scalarCurvature gradPotentialNormSq scaledScalarCurvature
      scaledGradPotentialNormSq potential : M -> Real}
    (hmeasure :
      perelmanWeightedMeasure scaledMu n (c * tau) potential =
        perelmanWeightedMeasure mu n tau potential)
    (hscalar : ∀ x : M, c * scaledScalarCurvature x = scalarCurvature x)
    (hgrad : ∀ x : M, c * scaledGradPotentialNormSq x = gradPotentialNormSq x) :
    wFunctional scaledMu n (c * tau) scaledScalarCurvature
        scaledGradPotentialNormSq potential =
      wFunctional mu n tau scalarCurvature gradPotentialNormSq potential :=
  wFunctional_scale_invariant_of_weightedMeasure_eq hmeasure hscalar hgrad

/-- MSM135 Chapter 6.1, unnumbered diffeomorphism-invariance property of `W`.

This is a measure-theoretic change-of-variables wrapper.  The metric layer
should later supply `hmeasure` from pullback volume and identify the pulled-back
scalar and gradient-square terms. -/
theorem w_entropy_diffeomorphism_invariance [MeasurableSpace M]
    {mu pullbackMu : Measure M} {n : Nat} {tau : Real}
    {scalarCurvature gradPotentialNormSq potential : M -> Real} (phi : M -> M)
    (hphi :
      AEMeasurable phi
        (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x))))
    (hbracket :
      AEStronglyMeasurable
        (wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential)
        (perelmanWeightedMeasure mu n tau potential))
    (hmeasure :
      Measure.map phi
          (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x))) =
        perelmanWeightedMeasure mu n tau potential) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      wFunctional pullbackMu n tau (fun x => scalarCurvature (phi x))
        (fun x => gradPotentialNormSq (phi x)) (fun x => potential (phi x)) :=
  wFunctional_diffeomorphism_invariant_of_map phi hphi hbracket hmeasure

/-- MSM135 Chapter 6.1, label `notes_and_commentary:lbl549`.

This records the scalar factor in
`delta (u dmu) = (-n*zeta/(2*tau) - h + V/2) u dmu`. -/
theorem lbl549_weighted_measure_variation_factor {n : Nat} {tau zeta : Real}
    (potentialVariation metricVariationTrace : M -> Real) :
    wEntropyWeightedMeasureVariationFactor n tau zeta potentialVariation
        metricVariationTrace =
      fun x : M =>
        -((n : Real) / (2 * tau)) * zeta - potentialVariation x +
          metricVariationTrace x / 2 := rfl

/-- MSM135 Chapter 6.1, label `notes_and_commentary:lbl550`. -/
theorem lbl550_weighted_measure_preserving_variation {n : Nat}
    {tau zeta : Real} {potentialVariation metricVariationTrace : M -> Real}
    (h :
      WEntropyWeightedMeasurePreservingVariation n tau zeta
        potentialVariation metricVariationTrace) :
    WEntropyWeightedMeasurePreservingVariation n tau zeta
      potentialVariation metricVariationTrace := h

/-- MSM135 Chapter 6.1, labels `notes_and_commentary:lbl551` and
`notes_and_commentary:lbl552`, Lemma 6.1.

This wrapper is the proved algebraic final step of the book proof: the combined
pre-IBP variation formula plus
`integral (Delta f - |grad f|^2) u dmu = 0` gives the final displayed
first-variation formula. -/
theorem lbl551_entropy_first_variation_lemma61_of_preIBP [MeasurableSpace M]
    {weightedMeasure : Measure M} {n : Nat} {tau zeta firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (htau : tau ≠ 0)
    (hpre :
      firstVariation =
        ∫ x, wEntropyFirstVariationPreIBPIntegrand n tau zeta
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
          ∂weightedMeasure)
    (hmetricRicciHess :
      ∀ᵐ x ∂weightedMeasure,
        metricRicciHess x = scalarCurvature x + lapPotential x)
    (hfinal_int :
      Integrable
        (fun x =>
          wEntropyFirstVariationLemma61Integrand n tau zeta
            scalarCurvature lapPotential gradPotentialNormSq potential
            potentialVariation metricVariationTrace metricVariationRicciHess
            metricRicciHess x)
        weightedMeasure)
    (hibp_int :
      Integrable
        (fun x =>
          (((n : Real) - 1) * zeta) *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure = 0) :
    firstVariation =
      ∫ x, wEntropyFirstVariationLemma61Integrand n tau zeta
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure :=
  wEntropyFirstVariation_lemma61_of_preIBP
    (M := M) (weightedMeasure := weightedMeasure) htau hpre
    hmetricRicciHess hfinal_int hibp_int hibp

/-- MSM135 Chapter 6.1, Lemma 6.1 with the left side interpreted as the
actual derivative of the W functional along a one-parameter path. -/
theorem lbl551_entropy_first_variation_actual_derivative_of_preIBP
    [MeasurableSpace M]
    {muPath : Real -> Measure M} {n : Nat} {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {weightedMeasure : Measure M} {s0 tau zeta firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (hderiv :
      WEntropyHasFirstVariationAt muPath n tauPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 firstVariation)
    (htau : tau ≠ 0)
    (hpre :
      firstVariation =
        ∫ x, wEntropyFirstVariationPreIBPIntegrand n tau zeta
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
          ∂weightedMeasure)
    (hmetricRicciHess :
      ∀ᵐ x ∂weightedMeasure,
        metricRicciHess x = scalarCurvature x + lapPotential x)
    (hfinal_int :
      Integrable
        (fun x =>
          wEntropyFirstVariationLemma61Integrand n tau zeta
            scalarCurvature lapPotential gradPotentialNormSq potential
            potentialVariation metricVariationTrace metricVariationRicciHess
            metricRicciHess x)
        weightedMeasure)
    (hibp_int :
      Integrable
        (fun x =>
          (((n : Real) - 1) * zeta) *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure = 0) :
    wEntropyFirstVariation muPath n tauPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 =
      ∫ x, wEntropyFirstVariationLemma61Integrand n tau zeta
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure :=
  wEntropyFirstVariation_eq_lemma61_of_hasFirstVariationAt_preIBP
    (M := M) (weightedMeasure := weightedMeasure) hderiv htau hpre
    hmetricRicciHess hfinal_int hibp_int hibp

/-- MSM135 Chapter 6.1, label `notes_and_commentary:lbl549`.

Book-facing alias for the pointwise producer differentiating
`u = (4*pi*tau)^(-n/2) * exp (-f)`. -/
abbrev lbl549_density_variation_producer :=
  @perelmanDensity_hasDerivAt

/-- MSM135 Chapter 6.1, label `notes_and_commentary:lbl551`.

Book-facing alias for the scalar derivative of
`tau * (R + |grad f|^2) + f - n`. -/
abbrev lbl551_bracket_variation_producer :=
  @wEntropyBracket_hasDerivAt

/-- MSM135 Chapter 6.1, labels `notes_and_commentary:lbl551`-`lbl552`.

Book-facing alias for the moving-volume producer that turns the scalar
derivative data into `WEntropyHasFirstVariationAt`. -/
abbrev lbl551_entropy_first_variation_producer_of_volumeVariation :=
  @WEntropyHasFirstVariationAt_of_volumeVariation

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the concrete measure-theoretic `F` functional. -/
abbrev lbl453_f_functional := @fFunctional

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the tau-free density derivative
`d(e^{-f_s})/ds = -h e^{-f}`. -/
abbrev lbl453_exp_density_variation_producer :=
  @expNegPotentialDensity_hasDerivAt

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the tau-free moving-volume producer
`delta(e^{-f} dmu) = (V/2 - h)e^{-f} dmu`. -/
abbrev lbl453_exp_weighted_measure_variation_producer :=
  @expWeightedMeasureIntegral_hasDerivAt_at

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the `F` first-variation producer from scalar derivative
data and moving-volume differentiation. -/
abbrev lbl453_f_first_variation_producer_of_volumeVariation :=
  @FFunctionalHasFirstVariationAt_of_volumeVariation

/-- MSM135 Chapter 6.1, weighted integration-by-parts identity used in
Lemma 6.1.

Book-facing alias for
`integral (Delta f - |grad f|^2) d(e^{-f}mu_g) = 0`. -/
abbrev lbl552_weighted_ibp :=
  @weightedIBP

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the arbitrary-test weighted Green identity against
`e^{-f} dmu_g`. -/
abbrev lbl453_weighted_green :=
  @weightedGreen

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for canceling the closed density-weighted divergence term. -/
abbrev lbl453_weighted_divergence_zero :=
  @weightedDivZero

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the shifted Hessian trace integral identity. -/
abbrev lbl453_shifted_trace_green :=
  @shiftIntEq

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the final integral statement of formula 5.10. -/
abbrev lbl453_f_formula510_statement :=
  @FFunctionalFormula510

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for assembling formula 5.10 from divergence cancellation
and the shifted-trace Green identity. -/
abbrev lbl453_f_formula510_assembly :=
  @formula510_of_ints

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the same assembly after the connection-trace vector field
has been constructed as `tr_g A`. -/
abbrev lbl453_f_formula510_trace_field :=
  @formula510_of_connTraceField

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the intrinsic trace-field assembly after replacing the
abstract `rawTrace` and `actionTrace` inputs by the constructed field's own
divergence and action. -/
abbrev lbl453_f_formula510_trace_intrinsic :=
  @formula510_of_trace

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the coordinate realization of `(tr_g A)(f)`. -/
abbrev lbl453_f_formula510_trace_action :=
  @connTraceAction_eq_gamma

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the finite-sum algebra contracting
`nabla_p A^p_ij - A^p_ij partial_p f` by `g^{ij}`. -/
abbrev lbl453_f_formula510_weighted_trace :=
  @weightedTrace_eq

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for reducing the final weighted-divergence trace to the
single raw divergence bridge for `tr_g A`. -/
abbrev lbl453_f_formula510_weighted_trace_raw :=
  @weightedTrace_of_raw

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the fixed-chart coefficient of the constructed trace
field `tr_g A`. -/
abbrev lbl453_f_formula510_trace_chart :=
  @connTraceChartCoeff_eventually

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the Voss-Weyl chart expansion of
`divergence_g(tr_g A)`. -/
abbrev lbl453_f_formula510_trace_voss :=
  @connTraceRawDiv_voss

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the product-rule split of the Voss-Weyl chart expansion
of `divergence_g(tr_g A)`. -/
abbrev lbl453_f_formula510_trace_product :=
  @connTraceRawDiv_chart_product

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the model-chart coefficient identity of the constructed
trace field `tr_g A`. -/
abbrev lbl453_f_formula510_trace_chart_onE :=
  @connTraceChartCoeffOnE_eventually

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for differentiating the explicit chart coefficient of
`tr_g A`. -/
abbrev lbl453_f_formula510_trace_chart_partial :=
  @connTraceChartCoeff_partial

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the center value of the constructed trace-field chart
coefficient. -/
abbrev lbl453_f_formula510_trace_chart_center :=
  @connTraceChartCoeff_center

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the explicit Voss-Weyl expansion of
`div(tr_g A)`, with chart coefficients replaced by
`g^{ij} A^p_ij`. -/
abbrev lbl453_f_formula510_trace_explicit :=
  @connTraceRawDiv_chart_explicit

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias converting a proved formula 5.10 identity for the derivative
value into an identity for the `deriv`-based first variation. -/
abbrev lbl453_f_formula510_final :=
  @fFunctionalFirstVariation_eq_formula510_of_hasFirstVariationAt

/-- MSM135 Chapter 5, formula 5.10, used in Chapter 6.1 Lemma 6.1.

Book-facing alias for the canonical path-based first variation formulation
`delta_(v,h) F(g,f)`.  The lower component formulas above are now proof-layer
producers feeding this endpoint, not the definition of variation. -/
abbrev lbl453_f_formula510_canonical_variation :=
  @f_firstVariation_formula510

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl551` and
`notes_and_commentary:lbl552`. -/
theorem lbl551_entropy_first_variation {D : WFirstVariationData M}
    (h : WEntropyFirstVariationFormula D) :
    WEntropyFirstVariationFormula D := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl553`-`lbl555`. -/
theorem lbl553_w_gradient_flow_system {S : WGradientFlowSystem M}
    (hmetric : S.metricEquation)
    (hpotential : S.potentialEquation)
    (htau : S.tauEquation) :
    S.metricEquation ∧ S.potentialEquation ∧ S.tauEquation :=
  ⟨hmetric, hpotential, htau⟩

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl556` and
`notes_and_commentary:lbl557`. -/
theorem lbl556_entropy_monotonicity_for_gradient_flow
    {W Wderiv rhs : Real -> Real} {timeSet : Set Real}
    (hderiv : WEntropyDerivativeFormula Wderiv rhs timeSet)
    (hmono : WEntropyMonotoneOn W timeSet) :
    WEntropyDerivativeFormula Wderiv rhs timeSet ∧ WEntropyMonotoneOn W timeSet :=
  ⟨hderiv, hmono⟩

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl558`-`lbl563`. -/
theorem lbl563_w_entropy_ricci_flow_monotonicity
    {W Wderiv rhs : Real -> Real} {timeSet : Set Real}
    (hderiv : WEntropyDerivativeFormula Wderiv rhs timeSet)
    (hmono : WEntropyMonotoneOn W timeSet) :
    WEntropyDerivativeFormula Wderiv rhs timeSet ∧ WEntropyMonotoneOn W timeSet :=
  ⟨hderiv, hmono⟩

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl573`-`lbl587`. -/
theorem lbl573_epsilon_entropy_formula {epsilon : Real} {n : Nat}
    {S : WeightedEntropyState M} {integral value : Real}
    (h : EpsilonEntropyFormula (M := M) epsilon n S integral value) :
    EpsilonEntropyFormula (M := M) epsilon n S integral value := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl594`-`lbl596`. -/
theorem lbl594_epsilon_entropy_lower_bound {epsilon lower value : Real}
    (h : EpsilonEntropyLowerBound epsilon lower value) :
    EpsilonEntropyLowerBound epsilon lower value := h

end

end Section01
end Chapter06
end MSM135
end BK
