import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Perelman's `W`-entropy as a weighted Bochner integral, and its proven invariances

This file builds Perelman's `W`-entropy functional concretely as a Bochner integral of a
scalar bracket against the weighted measure `u dμ`, with `u = (4πτ)^(-n/2) e^{-f}`, and
records the algebraic / measure-theoretic identities that are provable at this level:

* scale invariance of `W` from a `withDensity`-measure identity plus the scaling laws of the
  scalar-curvature and gradient-norm-squared inputs;
* diffeomorphism invariance of `W` through the measure-theoretic change of variables
  `MeasureTheory.integral_map`;
* the first variation of `W` along a one-parameter path as a genuine `HasDerivAt`/`deriv`;
* the final algebraic step of Lemma 6.1 (Chow–Lu–Ni, MSM135): once the three displayed
  variation contributions are combined into a pre-integration-by-parts integrand and the
  weighted identity `∫ (Δf - |∇f|²) u dμ = 0` is supplied, the result is the displayed
  Lemma-6.1 integrand.

The genuinely geometric inputs (scalar curvature, `|∇f|²`, the Riemannian volume measure, the
moving-volume derivative, and the weighted integration-by-parts identity) are kept as explicit
function/measure/hypothesis arguments; they are not derived here. Everything in this file is a
real Bochner integral or a real algebraic identity, conditional only on the supplied
measure/scaling/integrability hypotheses.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open MeasureTheory

variable {M : Type*}

/-! ## Concrete `W` functional integrand -/

/-- The scalar prefactor `(4 * π * τ)^(-n / 2)` in Perelman's density. -/
def perelmanDensityPrefactor (n : Nat) (tau : Real) : Real :=
  Real.rpow (4 * Real.pi * tau) (-(n : Real) / 2)

/-- Perelman's weighted density `u = (4πτ)^(-n/2) * exp (-f)`. -/
def perelmanDensity (n : Nat) (tau : Real) (potential : M -> Real) : M -> Real :=
  fun x => perelmanDensityPrefactor n tau * Real.exp (-(potential x))

/-- The measure `u dμ` used in the concrete `W` functional. -/
def perelmanWeightedMeasure [MeasurableSpace M] (mu : Measure M) (n : Nat)
    (tau : Real) (potential : M -> Real) : Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (perelmanDensity n tau potential x)

/-- The pointwise bracket in Perelman's `W` entropy:
`τ * (R + |∇f|²) + f - n`. -/
def wEntropyBracket (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : M -> Real :=
  fun x =>
    tau * (scalarCurvature x + gradPotentialNormSq x) + potential x - (n : Real)

/-- Concrete measure-theoretic version of Perelman's `W` functional.  The
geometric input is intentionally component-free here: later metric-facing
producers should supply `scalarCurvature`, `gradPotentialNormSq`, and the
Riemannian volume measure. -/
def wFunctional [MeasurableSpace M] (mu : Measure M) (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : Real :=
  ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
    ∂(perelmanWeightedMeasure mu n tau potential)

/-- Unfolding form of the concrete `W` functional. -/
theorem wFunctional_eq_integral [MeasurableSpace M] (mu : Measure M) (n : Nat)
    (tau : Real) (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂(perelmanWeightedMeasure mu n tau potential) := rfl

/-- Rewrite Perelman's weighted `W` integral against the underlying measure.

The measurability hypothesis is only for the scalar density; no geometric or
regularity assumptions are hidden in this measure-theoretic conversion. -/
theorem wFunctional_base [MeasurableSpace M]
    (mu : Measure M) (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real)
    (htau : 0 ≤ tau)
    (hmeas : AEMeasurable
      (fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x)) mu) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      ∫ x, perelmanDensity n tau potential x *
        wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x ∂mu := by
  unfold wFunctional perelmanWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential)]
  apply integral_congr_ae
  filter_upwards with x
  have hnonneg : 0 ≤ perelmanDensity n tau potential x := by
    unfold perelmanDensity perelmanDensityPrefactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) htau) _)
      (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

private theorem wEntropyBracket_scale_eq {n : Nat} {tau c : Real}
    {scalarCurvature gradPotentialNormSq scaledScalarCurvature
      scaledGradPotentialNormSq potential : M -> Real}
    (hscalar : ∀ x : M, c * scaledScalarCurvature x = scalarCurvature x)
    (hgrad : ∀ x : M, c * scaledGradPotentialNormSq x = gradPotentialNormSq x)
    (x : M) :
    wEntropyBracket n (c * tau) scaledScalarCurvature
        scaledGradPotentialNormSq potential x =
      wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x := by
  unfold wEntropyBracket
  have hmain :
      (c * tau) * (scaledScalarCurvature x + scaledGradPotentialNormSq x) =
        tau * (scalarCurvature x + gradPotentialNormSq x) := by
    calc
      (c * tau) * (scaledScalarCurvature x + scaledGradPotentialNormSq x)
          = tau * (c * scaledScalarCurvature x + c * scaledGradPotentialNormSq x) := by
            ring
      _ = tau * (scalarCurvature x + gradPotentialNormSq x) := by
            rw [hscalar x, hgrad x]
  rw [hmain]

/-- Scale invariance of the concrete `W` functional, isolated at the interface
level that the current geometry can justify.

For the geometric specialization `scaledMu` is the Riemannian measure of `c g`,
`scaledScalarCurvature` is `R_{c g}`, and `scaledGradPotentialNormSq` is
`|∇_{c g} f|²`.  The hypotheses are exactly the scaling laws needed to turn
this into the book statement `W(cg,f,c*τ) = W(g,f,τ)`. -/
theorem wFunctional_scale_invariant_of_weightedMeasure_eq [MeasurableSpace M]
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
      wFunctional mu n tau scalarCurvature gradPotentialNormSq potential := by
  unfold wFunctional
  rw [hmeasure]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun x =>
    wEntropyBracket_scale_eq (M := M) hscalar hgrad x

/-- Diffeomorphism invariance of the concrete `W` functional through the
measure-theoretic change-of-variables interface.

The map `phi` is the diffeomorphism on points.  A later metric-facing producer
should prove `hmeasure` for the pulled-back metric and volume form, and should
identify the pulled-back scalar and gradient-square terms with composition by
`phi`. -/
theorem wFunctional_diffeomorphism_invariant_of_map [MeasurableSpace M]
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
        (fun x => gradPotentialNormSq (phi x)) (fun x => potential (phi x)) := by
  unfold wFunctional
  have hbracket_map :
      AEStronglyMeasurable
        (wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential)
        (Measure.map phi
          (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x)))) := by
    rw [hmeasure]
    exact hbracket
  calc
    (∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂perelmanWeightedMeasure mu n tau potential)
        =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂Measure.map phi
          (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x))) := by
        rw [hmeasure]
    _ =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential (phi x)
        ∂perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x)) :=
        MeasureTheory.integral_map hphi hbracket_map
    _ =
      ∫ x, wEntropyBracket n tau (fun y => scalarCurvature (phi y))
          (fun y => gradPotentialNormSq (phi y)) (fun y => potential (phi y)) x
        ∂perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x)) := rfl

/-! ## First variation as an actual derivative -/

/-- The real-valued `W` functional along a one-parameter scalar/measure path.

This is the first place where the formalization uses an actual derivative of
the functional.  A metric-facing path `g_s` should later supply the measure
path, scalar-curvature path, gradient-square path, and potential path. -/
def wFunctionalAlong [MeasurableSpace M] (mu : Real -> Measure M) (n : Nat)
    (tau : Real -> Real)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real) :
    Real -> Real :=
  fun s =>
    wFunctional (mu s) n (tau s) (scalarCurvature s)
      (gradPotentialNormSq s) (potential s)

/-- `firstVariation` is the actual derivative of `W` along the supplied path at
`s0`. -/
def WEntropyHasFirstVariationAt [MeasurableSpace M] (mu : Real -> Measure M)
    (n : Nat) (tau : Real -> Real)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 firstVariation : Real) : Prop :=
  HasDerivAt
    (wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential)
    firstVariation s0

/-- The actual first variation of `W` along a path, defined as the real
derivative of `wFunctionalAlong`. -/
def wEntropyFirstVariation [MeasurableSpace M] (mu : Real -> Measure M)
    (n : Nat) (tau : Real -> Real)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 : Real) : Real :=
  deriv (wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential) s0

/-- If a path has a first variation in the `HasDerivAt` sense, the `deriv`-based
definition returns that value. -/
theorem wEntropyFirstVariation_eq_of_hasFirstVariationAt [MeasurableSpace M]
    {mu : Real -> Measure M} {n : Nat} {tau : Real -> Real}
    {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}
    {s0 firstVariation : Real}
    (h :
      WEntropyHasFirstVariationAt mu n tau scalarCurvature gradPotentialNormSq
        potential s0 firstVariation) :
    wEntropyFirstVariation mu n tau scalarCurvature gradPotentialNormSq
        potential s0 = firstVariation := by
  unfold wEntropyFirstVariation WEntropyHasFirstVariationAt at *
  exact h.deriv

/-! ## First variation of `W` (Lemma 6.1, algebraic final step) -/

/-- The combined pre-integration-by-parts integrand in the proof of Lemma 6.1.

The inputs are scalar contractions:
* `metricVariationRicciHess` is `v_ij * (Ric_ij + Hess_ij f)`;
* `metricVariationTrace` is `V = tr_g v`;
* `lapPotential` is `Δf`;
* `gradPotentialNormSq` is `|∇f|²`.

This is the expression obtained after combining the three displayed variation
formulas, before rewriting it into the final Lemma 6.1 form. -/
def wEntropyFirstVariationPreIBPIntegrand (n : Nat) (tau tauVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess : M -> Real) :
    M -> Real :=
  fun x =>
    -tau * metricVariationRicciHess x +
      tau * (metricVariationTrace x / 2 - potentialVariation x) *
        (2 * lapPotential x - gradPotentialNormSq x + scalarCurvature x +
          (potential x - (n : Real)) / tau) +
      (potentialVariation x +
        (1 - (n : Real) / 2) * tauVariation *
          (scalarCurvature x + gradPotentialNormSq x) -
        ((n : Real) * tauVariation) / (2 * tau) *
          (potential x - (n : Real)))

/-- The scalar-contracted final integrand in Lemma 6.1.

The input `metricRicciHess` is the contraction
`g_ij * (Ric_ij + Hess_ij f)`, later supplied geometrically as
`R + Δf`.  The first line of the book's formula is represented by the
expanded scalar contraction
`(-τ v + ζ g) * (Ric + Hess f - (1 / (2 τ)) g)`. -/
def wEntropyFirstVariationLemma61Integrand (n : Nat) (tau tauVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real) : M -> Real :=
  fun x =>
    (-tau * metricVariationRicciHess x + tauVariation * metricRicciHess x +
        metricVariationTrace x / 2 -
        ((n : Real) * tauVariation) / (2 * tau)) +
      tau *
        (metricVariationTrace x / 2 - potentialVariation x -
          ((n : Real) * tauVariation) / (2 * tau)) *
        (scalarCurvature x + 2 * lapPotential x - gradPotentialNormSq x +
          (potential x - (n : Real) - 1) / tau)

private theorem wEntropyFirstVariationPreIBPIntegrand_eq_lemma61_add_ibp
    {n : Nat} {tau tauVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (htau : tau ≠ 0) {x : M}
    (hmetricRicciHess :
      metricRicciHess x = scalarCurvature x + lapPotential x) :
    wEntropyFirstVariationPreIBPIntegrand n tau tauVariation scalarCurvature
        lapPotential gradPotentialNormSq potential potentialVariation
        metricVariationTrace metricVariationRicciHess x =
      wEntropyFirstVariationLemma61Integrand n tau tauVariation scalarCurvature
          lapPotential gradPotentialNormSq potential potentialVariation
          metricVariationTrace metricVariationRicciHess metricRicciHess x +
        (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x) := by
  unfold wEntropyFirstVariationPreIBPIntegrand
    wEntropyFirstVariationLemma61Integrand
  rw [hmetricRicciHess]
  field_simp [htau]
  ring

/-- Lemma 6.1, formalized as the algebraic final step of the proof.

This theorem proves the book's last step: once the three variation inputs have
been combined into `wEntropyFirstVariationPreIBPIntegrand`, and once the
weighted integration-by-parts identity
`∫ (Δf - |∇f|²) u dμ = 0` is available, the result is exactly
the final integrand.

The remaining geometric frontiers are the producers for the three variation
inputs and the weighted integration-by-parts identity. -/
theorem wEntropyFirstVariation_lemma61_of_preIBP [MeasurableSpace M]
    {weightedMeasure : Measure M} {n : Nat} {tau tauVariation firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (htau : tau ≠ 0)
    (hpre :
      firstVariation =
        ∫ x, wEntropyFirstVariationPreIBPIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
          ∂weightedMeasure)
    (hmetricRicciHess :
      ∀ᵐ x ∂weightedMeasure,
        metricRicciHess x = scalarCurvature x + lapPotential x)
    (hfinal_int :
      Integrable
        (fun x =>
          wEntropyFirstVariationLemma61Integrand n tau tauVariation
            scalarCurvature lapPotential gradPotentialNormSq potential
            potentialVariation metricVariationTrace metricVariationRicciHess
            metricRicciHess x)
        weightedMeasure)
    (hibp_int :
      Integrable
        (fun x =>
          (((n : Real) - 1) * tauVariation) *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure = 0) :
    firstVariation =
      ∫ x, wEntropyFirstVariationLemma61Integrand n tau tauVariation
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure := by
  rw [hpre]
  have hpoint :
      (fun x =>
        wEntropyFirstVariationPreIBPIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x)
        =ᵐ[weightedMeasure]
      fun x =>
        wEntropyFirstVariationLemma61Integrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x +
        (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x) := by
    filter_upwards [hmetricRicciHess] with x hx
    exact wEntropyFirstVariationPreIBPIntegrand_eq_lemma61_add_ibp
      (M := M) (n := n) (tauVariation := tauVariation) htau hx
  calc
    (∫ x, wEntropyFirstVariationPreIBPIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
        ∂weightedMeasure)
        =
      ∫ x,
        wEntropyFirstVariationLemma61Integrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x +
        (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x)
        ∂weightedMeasure := integral_congr_ae hpoint
    _ =
      (∫ x, wEntropyFirstVariationLemma61Integrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x ∂weightedMeasure) +
        ∫ x, (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure := by
        rw [integral_add hfinal_int hibp_int]
    _ =
      (∫ x, wEntropyFirstVariationLemma61Integrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x ∂weightedMeasure) +
        (((n : Real) - 1) * tauVariation) *
          ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure := by
        rw [integral_const_mul]
    _ =
      ∫ x, wEntropyFirstVariationLemma61Integrand n tau tauVariation
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure := by
        rw [hibp, mul_zero, add_zero]

/-- Lemma 6.1 with the left-hand side represented by the actual derivative
`wEntropyFirstVariation` of a `W`-path. -/
theorem wEntropyFirstVariation_eq_lemma61_of_hasFirstVariationAt_preIBP
    [MeasurableSpace M]
    {muPath : Real -> Measure M} {n : Nat} {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {weightedMeasure : Measure M} {s0 tau tauVariation firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (hderiv :
      WEntropyHasFirstVariationAt muPath n tauPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 firstVariation)
    (htau : tau ≠ 0)
    (hpre :
      firstVariation =
        ∫ x, wEntropyFirstVariationPreIBPIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
          ∂weightedMeasure)
    (hmetricRicciHess :
      ∀ᵐ x ∂weightedMeasure,
        metricRicciHess x = scalarCurvature x + lapPotential x)
    (hfinal_int :
      Integrable
        (fun x =>
          wEntropyFirstVariationLemma61Integrand n tau tauVariation
            scalarCurvature lapPotential gradPotentialNormSq potential
            potentialVariation metricVariationTrace metricVariationRicciHess
            metricRicciHess x)
        weightedMeasure)
    (hibp_int :
      Integrable
        (fun x =>
          (((n : Real) - 1) * tauVariation) *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure = 0) :
    wEntropyFirstVariation muPath n tauPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 =
      ∫ x, wEntropyFirstVariationLemma61Integrand n tau tauVariation
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure := by
  rw [wEntropyFirstVariation_eq_of_hasFirstVariationAt hderiv]
  exact wEntropyFirstVariation_lemma61_of_preIBP
    (M := M) (weightedMeasure := weightedMeasure) htau hpre
    hmetricRicciHess hfinal_int hibp_int hibp

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
