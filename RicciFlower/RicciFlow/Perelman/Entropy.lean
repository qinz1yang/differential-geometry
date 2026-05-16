/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Perelman entropy statement interfaces

This file records the first RicciFlower-native vocabulary for MSM135 Chapter 6.
The definitions are intentionally lightweight: they preserve the mathematical
shape of the entropy, `mu`, `nu`, logarithmic Sobolev, and variation statements
without pretending that the measure-theoretic and global analytic infrastructure
has already been formalized.
-/

namespace RicciFlower
namespace RicciFlow
namespace Perelman

noncomputable section

open MeasureTheory

variable {M : Type*}

/-! ## Concrete `W` functional integrand -/

/-- The scalar prefactor `(4 * pi * tau)^(-n / 2)` in Perelman's density. -/
def perelmanDensityPrefactor (n : Nat) (tau : Real) : Real :=
  Real.rpow (4 * Real.pi * tau) (-(n : Real) / 2)

/-- Perelman's weighted density `u = (4*pi*tau)^(-n/2) * exp (-f)`. -/
def perelmanDensity (n : Nat) (tau : Real) (potential : M -> Real) : M -> Real :=
  fun x => perelmanDensityPrefactor n tau * Real.exp (-(potential x))

/-- The measure `u dmu` used in the concrete `W` functional. -/
def perelmanWeightedMeasure [MeasurableSpace M] (mu : Measure M) (n : Nat)
    (tau : Real) (potential : M -> Real) : Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (perelmanDensity n tau potential x)

/-- The pointwise bracket in Perelman's `W` entropy:
`tau * (R + |grad f|^2) + f - n`. -/
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
level that the current RicciFlower geometry can justify.

For the geometric specialization `scaledMu` is the Riemannian measure of `c g`,
`scaledScalarCurvature` is `R_{c g}`, and `scaledGradPotentialNormSq` is
`|grad_{c g} f|^2`.  The hypotheses are exactly the scaling laws needed to turn
this into the book statement `W(cg,f,c*tau) = W(g,f,tau)`. -/
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

/-! ## First variation of `W` -/

/-- The scalar factor in label `lbl549`:
`delta (u dmu) = firstVariationWeightedMeasureFactor * u dmu`.

Here `potentialVariation` is the book's `h`, `metricVariationTrace` is `V`,
and `tauVariation` is the constant `zeta`. -/
def wEntropyWeightedMeasureVariationFactor (n : Nat) (tau tauVariation : Real)
    (potentialVariation metricVariationTrace : M -> Real) : M -> Real :=
  fun x =>
    -((n : Real) / (2 * tau)) * tauVariation - potentialVariation x +
      metricVariationTrace x / 2

/-- Measure-preserving variations for the weighted measure, label `lbl550`. -/
def WEntropyWeightedMeasurePreservingVariation (n : Nat) (tau tauVariation : Real)
    (potentialVariation metricVariationTrace : M -> Real) : Prop :=
  ∀ x : M,
    wEntropyWeightedMeasureVariationFactor n tau tauVariation
      potentialVariation metricVariationTrace x = 0

/-- The combined pre-integration-by-parts integrand in the proof of Lemma 6.1.

The inputs are scalar contractions:
* `metricVariationRicciHess` is `v_ij * (Ric_ij + Hess_ij f)`;
* `metricVariationTrace` is `V = tr_g v`;
* `lapPotential` is `Delta f`;
* `gradPotentialNormSq` is `|grad f|^2`.

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

/-- The scalar-contracted final integrand in Lemma 6.1, label `lbl552`.

The input `metricRicciHess` is the contraction
`g_ij * (Ric_ij + Hess_ij f)`, later supplied geometrically as
`R + Delta f`.  The first line of the book's formula is represented by the
expanded scalar contraction
`(-tau v + zeta g) * (Ric + Hess f - (1 / (2 tau)) g)`. -/
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
`integral (Delta f - |grad f|^2) u dmu = 0` is available, the result is exactly
the final integrand in label `lbl552`.

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

/-- The scalar data entering Perelman's `W` entropy at one time.  The integral
and measure layer is kept outside this structure for now. -/
structure WeightedEntropyState (M : Type*) where
  tau : Real
  density : M -> Real
  potential : M -> Real
  scalarCurvature : M -> Real
  gradPotentialNormSq : M -> Real

/-- The positivity/normalization side conditions for the conjugate heat density
appearing in MSM135 Chapter 6, labels `lbl543` and `lbl545`. -/
def PositiveNormalizedDensity (_n : Nat) (S : WeightedEntropyState M) : Prop :=
  0 < S.tau ∧ ∀ x : M, 0 ≤ S.density x

/-- Statement-level form of the displayed `W` entropy formula, label `lbl544`.
The scalar `integral` is the value of the not-yet-formalized integral. -/
def WEntropyFormula (n : Nat) (S : WeightedEntropyState M)
    (integral value : Real) : Prop :=
  PositiveNormalizedDensity n S ∧ value = integral

/-- Inputs for the first variation formula for `W`, label `lbl551`. -/
structure WFirstVariationData (M : Type*) where
  metricVariationTrace : Real
  potentialVariation : Real
  tauVariation : Real
  constraintEquation : Prop
  firstVariationRHS : Real

/-- Predicate version of the first variation formula for `W`.  The current
frontier is the analytic proof that the RHS is the integral shown in the book. -/
def WEntropyFirstVariationFormula (D : WFirstVariationData M) : Prop :=
  D.constraintEquation

/-- The coupled flow equations associated to `W`, labels `lbl553`-`lbl555`,
`lbl558`-`lbl560`, and their Ricci-flow specialization. -/
structure WGradientFlowSystem (M : Type*) where
  metricEquation : Prop
  potentialEquation : Prop
  tauEquation : Prop

/-- Derivative formula for `W` along a flow, including the nonnegative square
term in labels `lbl557`, `lbl563`, `lbl569`, and `lbl587`. -/
def WEntropyDerivativeFormula (Wderiv rhs : Real -> Real)
    (timeSet : Set Real) : Prop :=
  ∀ t : Real, t ∈ timeSet -> Wderiv t = rhs t ∧ 0 ≤ rhs t

/-- Monotonicity interface for `W` along the relevant flow. -/
def WEntropyMonotoneOn (W : Real -> Real) (timeSet : Set Real) : Prop :=
  ∀ t₁ : Real, t₁ ∈ timeSet -> ∀ t₂ : Real, t₂ ∈ timeSet ->
    t₁ ≤ t₂ -> W t₁ ≤ W t₂

/-- The `epsilon`-unified entropy/energy formula from labels `lbl573`-`lbl587`. -/
def EpsilonEntropyFormula (epsilon : Real) (n : Nat)
    (S : WeightedEntropyState M) (integral value : Real) : Prop :=
  PositiveNormalizedDensity n S ∧ value = integral ∧ epsilon ∈ ({-1, 0, 1} : Set Real)

/-- Lower-bound predicate for `W_epsilon`, labels `lbl594`-`lbl596`. -/
def EpsilonEntropyLowerBound (epsilon lower value : Real) : Prop :=
  lower ≤ value ∧ epsilon ∈ ({-1, 0, 1} : Set Real)

/-- Book-level lower-bound meaning of `mu(g,tau)`, labels `lbl600`-`lbl603`. -/
def MuFunctionalLowerBound (admissible : Set (WeightedEntropyState M))
    (W : WeightedEntropyState M -> Real) (mu : Real) : Prop :=
  ∀ S : WeightedEntropyState M, S ∈ admissible -> mu ≤ W S

/-- Existence of a minimizer for `mu`, labels `lbl608`-`lbl612`. -/
def MuFunctionalHasMinimizer (admissible : Set (WeightedEntropyState M))
    (W : WeightedEntropyState M -> Real) (mu : Real) : Prop :=
  ∃ S : WeightedEntropyState M, S ∈ admissible ∧ W S = mu

/-- Monotonicity of `mu` under Ricci flow, labels `lbl613`-`lbl615`. -/
def MuMonotoneAlongRicciFlow (muAt : Real -> Real) (timeSet : Set Real) : Prop :=
  WEntropyMonotoneOn muAt timeSet

/-- Lower-bound meaning of Perelman's `nu` invariant, labels `lbl622`-`lbl626`. -/
def NuFunctionalLowerBound (muAtTau : Real -> Real) (nu : Real) : Prop :=
  ∀ tau : Real, 0 < tau -> nu ≤ muAtTau tau

/-- Existence of a minimizing scale for `nu`. -/
def NuFunctionalHasMinimizer (muAtTau : Real -> Real) (nu : Real) : Prop :=
  ∃ tau : Real, 0 < tau ∧ muAtTau tau = nu

/-- Monotonicity of `nu`, labels `lbl627`-`lbl629`. -/
def NuMonotoneAlongRicciFlow (nuAt : Real -> Real) (timeSet : Set Real) : Prop :=
  WEntropyMonotoneOn nuAt timeSet

/-- Statement interface for the Cheeger-Gromov behavior of `mu`, label `lbl618`. -/
def MuCheegerGromovConvergenceStatement (hypothesis conclusion : Prop) : Prop :=
  hypothesis -> conclusion

/-- Statement interface for "shrinking breathers are gradient shrinking
solitons", labels `lbl619`-`lbl621`. -/
def ShrinkingBreatherIsGradientSoliton (breather soliton : Prop) : Prop :=
  breather -> soliton

/-- Logarithmic Sobolev inequality interface, labels `lbl630`-`lbl645`. -/
def LogSobolevInequality (entropy energy constant : Real) : Prop :=
  entropy ≤ energy + constant

/-- Variational formula for the modified scalar curvature, labels
`lbl698`-`lbl704`. -/
def ModifiedScalarCurvatureVariation (lhs rhs : Real) : Prop :=
  lhs = rhs

/-- Second variation interface for the energy and entropy formulas, labels
`lbl705`-`lbl711`. -/
def EnergyEntropySecondVariationFormula (lhs rhs : Real) : Prop :=
  lhs = rhs

/-- Matrix Harnack formula for the adjoint heat equation, labels
`lbl712`-`lbl715`. -/
def MatrixHarnackAdjointHeatFormula (lhs rhs : Real) : Prop :=
  lhs = rhs

end

end Perelman
end RicciFlow
end RicciFlower
