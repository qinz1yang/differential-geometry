/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.Analysis.Green
import RicciFlower.LeviCivita.ChartDensity
import RicciFlower.LeviCivita.Variation
import RicciFlower.RicciFlow.Perelman.Variation
import RicciFlower.Tensor.RSTensor.MetricTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Perelman's `F` functional and formula 5.10 interfaces

This file starts the RicciFlower-native route to MSM135 formula 5.10.  It
contains the concrete measure-theoretic `F` functional, the low-risk
`e^{-f} dmu` variation producer, and explicit predicate handles for the
remaining Ricci/Hessian/divergence steps.
-/

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

/-! ## Concrete `F` functional -/

/-- The density `e^{-f}` used in Perelman's `F` functional. -/
def expNegPotentialDensity (potential : M -> Real) : M -> Real :=
  fun x => Real.exp (-(potential x))

/-- The weighted measure `e^{-f} dmu`. -/
def expNegPotentialWeightedMeasure [MeasurableSpace M] (mu : Measure M)
    (potential : M -> Real) : Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (expNegPotentialDensity potential x)

/-- Rewrite integrals against `e^{-f} dmu` as base-measure integrals with the
explicit density factor.  This is the measure-theoretic bridge used by the
closed Green/IBP identity in Perelman's formula 5.10 route. -/
theorem expNegPotentialWeightedMeasure_integral_eq_base
    [MeasurableSpace M] (mu : Measure M) (potential integrand : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu) :
    (∫ x, integrand x ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, expNegPotentialDensity potential x * integrand x ∂mu := by
  rw [expNegPotentialWeightedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    integrand]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnonneg : 0 ≤ expNegPotentialDensity potential x :=
    le_of_lt (Real.exp_pos _)
  simp [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

/-- Perelman-facing weighted exponential IBP bridge.  Once Green's identity and
the chain rule prove the base-density identity, this transports it to the
weighted measure `e^{-f}dmu`. -/
theorem expWeightedIBP_of_baseIntegral_zero [MeasurableSpace M]
    (mu : Measure M) (potential lapPotential gradPotentialNormSq : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu)
    (hbase :
      ∫ x,
        expNegPotentialDensity potential x *
          (lapPotential x - gradPotentialNormSq x)
        ∂mu = 0) :
    ∫ x, (lapPotential x - gradPotentialNormSq x)
      ∂(expNegPotentialWeightedMeasure mu potential) = 0 := by
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := mu) (potential := potential)
    (integrand := fun x : M => lapPotential x - gradPotentialNormSq x)
    hmeas]
  exact hbase

/-- The pointwise bracket `R + |grad f|^2` in Perelman's `F`. -/
def fFunctionalBracket (scalarCurvature gradPotentialNormSq : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + gradPotentialNormSq x

/-- The alternate closed-manifold bracket `R + Delta f` used in the proof of
formula 5.10. -/
def fFunctionalClosedBracket (scalarCurvature lapPotential : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + lapPotential x

/-- Scalar derivative of the closed bracket `R + Delta f`. -/
def fFunctionalClosedBracketVariation
    (scalarCurvatureVariation lapPotentialVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + lapPotentialVariation x

/-- Concrete measure-theoretic version of Perelman's `F` functional. -/
def fFunctional [MeasurableSpace M] (mu : Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : Real :=
  ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
    ∂(expNegPotentialWeightedMeasure mu potential)

/-- Unfolding form of the concrete `F` functional. -/
theorem fFunctional_eq_integral [MeasurableSpace M] (mu : Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    fFunctional mu scalarCurvature gradPotentialNormSq potential =
      ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
        ∂(expNegPotentialWeightedMeasure mu potential) := rfl

/-- `F` along a one-parameter scalar/measure path. -/
def fFunctionalAlong [MeasurableSpace M] (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real) :
    Real -> Real :=
  fun s => fFunctional (mu s) (scalarCurvature s) (gradPotentialNormSq s)
    (potential s)

/-- `F` has first variation `firstVariation` at `s0` along the supplied path. -/
def FFunctionalHasFirstVariationAt [MeasurableSpace M]
    (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 firstVariation : Real) : Prop :=
  HasDerivAt (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential)
    firstVariation s0

/-- The actual first variation of `F` along a path, defined as `deriv`. -/
def fFunctionalFirstVariation [MeasurableSpace M]
    (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 : Real) : Real :=
  deriv (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential) s0

theorem fFunctionalFirstVariation_eq_of_hasFirstVariationAt [MeasurableSpace M]
    {mu : Real -> Measure M}
    {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}
    {s0 firstVariation : Real}
    (h :
      FFunctionalHasFirstVariationAt mu scalarCurvature gradPotentialNormSq
        potential s0 firstVariation) :
    fFunctionalFirstVariation mu scalarCurvature gradPotentialNormSq potential s0 =
      firstVariation := by
  unfold fFunctionalFirstVariation FFunctionalHasFirstVariationAt at *
  exact h.deriv

/-! ## `e^{-f} dmu` variation producer -/

theorem expNegPotentialDensity_hasDerivAt
    {potentialPath : Real -> M -> Real} {s0 : Real}
    {potentialVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real => expNegPotentialDensity (potentialPath s) x)
      (-(potentialVariation x) *
        expNegPotentialDensity (potentialPath s0) x)
      s0 := by
  have h := (hpotential_deriv x).neg.exp
  simpa [expNegPotentialDensity, mul_comm, mul_left_comm, mul_assoc] using h

/-- The scalar factor in
`delta(e^{-f} dmu) = (V/2 - h) e^{-f} dmu`. -/
def expWeightedMeasureVariationFactor
    (potentialVariation metricVariationTrace : M -> Real) : M -> Real :=
  fun x => metricVariationTrace x / 2 - potentialVariation x

/-- The base-measure integrand produced by differentiating
`e^{-f_s} * phi_s dmu_s`. -/
def expWeightedIntegralVariationIntegrand
    (potential potentialVariation metricVariationTrace phi phiVariation :
      M -> Real) :
    M -> Real :=
  fun x =>
    expNegPotentialDensity potential x *
      (phiVariation x +
        phi x *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Perelman-facing weighted identity
`∫ (Delta f - |grad f|^2) e^{-f} dmu_g = 0`, obtained from the closed
Green identity and the pointwise chain rule for `grad(exp(-f))`. -/
theorem weightedIBP
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlap :
      Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
      (RicciFlower.Analysis.DivergenceTheorem.Δ_g
          (I := I) g hpotential x -
        g.inner x
          ((RicciFlower.Analysis.DivergenceTheorem.grad_g
            (I := I) g hpotential :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((RicciFlower.Analysis.DivergenceTheorem.grad_g
            (I := I) g hpotential :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  apply expWeightedIBP_of_baseIntegral_zero
    (mu := riemannianVolumeMeasure (I := I) (M := M) g)
    (potential := potential)
    (lapPotential :=
      RicciFlower.Analysis.DivergenceTheorem.Δ_g
        (I := I) g hpotential)
    (gradPotentialNormSq := fun x : M =>
      g.inner x
        ((RicciFlower.Analysis.DivergenceTheorem.grad_g
          (I := I) g hpotential :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((RicciFlower.Analysis.DivergenceTheorem.grad_g
          (I := I) g hpotential :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
  · exact hmeas
  · simpa [expNegPotentialDensity] using
      RicciFlower.Analysis.DivergenceTheorem.expNegIBP
        (I := I) g hpotential hlap hgrad

/-- Scalar consequence of weighted integration by parts:
if `∫(Delta f - |grad f|^2)e^{-f}dmu = 0`, then the two bracket forms of
Perelman's `F` have the same weighted integral. -/
theorem bracket_eq_closed_of_ibp [MeasurableSpace M]
    (mu : Measure M)
    (scalarCurvature lapPotential gradPotentialNormSq potential : M -> Real)
    (hscalar_int :
      Integrable scalarCurvature
        (expNegPotentialWeightedMeasure mu potential))
    (hlap_int :
      Integrable lapPotential
        (expNegPotentialWeightedMeasure mu potential))
    (hgrad_int :
      Integrable gradPotentialNormSq
        (expNegPotentialWeightedMeasure mu potential))
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure mu potential) = 0) :
    (∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
      ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, fFunctionalClosedBracket scalarCurvature lapPotential x
        ∂(expNegPotentialWeightedMeasure mu potential) := by
  let μw := expNegPotentialWeightedMeasure mu potential
  have hdiff :
      (∫ x, lapPotential x ∂μw) =
        ∫ x, gradPotentialNormSq x ∂μw := by
    have hsub :
        (∫ x, (lapPotential x - gradPotentialNormSq x) ∂μw) =
          (∫ x, lapPotential x ∂μw) -
            ∫ x, gradPotentialNormSq x ∂μw := by
      exact integral_sub hlap_int hgrad_int
    rw [hsub] at hibp
    linarith
  calc
    (∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x ∂μw)
        =
      ∫ x, scalarCurvature x + gradPotentialNormSq x ∂μw := by
        rfl
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, gradPotentialNormSq x ∂μw := by
        exact integral_add hscalar_int hgrad_int
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, lapPotential x ∂μw := by
        rw [hdiff]
    _ =
      ∫ x, scalarCurvature x + lapPotential x ∂μw := by
        exact (integral_add hscalar_int hlap_int).symm
    _ =
      ∫ x, fFunctionalClosedBracket scalarCurvature lapPotential x ∂μw := by
        rfl

/-- Arbitrary-test weighted Green identity transported to the weighted measure
`e^{-f} dmu_g`. -/
theorem weightedGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
        RicciFlower.Analysis.DivergenceTheorem.Δ_g
          (I := I) g hq x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        q x *
          (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x +
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let gradSq : M -> Real := fun x =>
    g.inner x
      ((RicciFlower.Analysis.DivergenceTheorem.grad_g
        (I := I) g hpotential :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((RicciFlower.Analysis.DivergenceTheorem.grad_g
        (I := I) g hpotential :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      RicciFlower.Analysis.DivergenceTheorem.Δ_g (I := I) g hq x)
    hmeas]
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      q x *
        (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x + gradSq x))
    hmeas]
  calc
    ∫ x,
        expNegPotentialDensity potential x *
          RicciFlower.Analysis.DivergenceTheorem.Δ_g (I := I) g hq x ∂μ =
      ∫ x,
        q x *
          (expNegPotentialDensity potential x *
            (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x + gradSq x)) ∂μ := by
      simpa [μ, expNegPotentialDensity, gradSq] using
        RicciFlower.Analysis.DivergenceTheorem.expNegGreen
          (I := I) g hpotential hq
    _ =
      ∫ x,
        expNegPotentialDensity potential x *
          (q x *
            (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x + gradSq x)) ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      ring

/-- Closed weighted-divergence cancellation.  If a scalar term becomes the
ordinary divergence after multiplying by `e^{-f}`, then its weighted integral
vanishes. -/
theorem weightedDivZero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace : M -> Real}
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdiv :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g X x =
          expNegPotentialDensity potential x * weightedDivergenceTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := weightedDivergenceTrace) hmeas]
  calc
    ∫ x, expNegPotentialDensity potential x * weightedDivergenceTrace x ∂μ =
        ∫ x, RicciFlower.Analysis.DivergenceTheorem.divergence_g
          (I := I) g X x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hdiv x).symm
    _ = 0 := by
      simpa [μ] using
        RicciFlower.Analysis.DivergenceTheorem.integral_divergence_eq_zero_of_compact
          (I := I) g X

/-- Smoothness of Perelman's density `e^{-f}`. -/
theorem expNegPotentialDensity_contMDiff
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) :
    ContMDiff I 𝓘(Real, Real) ∞ (expNegPotentialDensity potential) := by
  simpa [expNegPotentialDensity] using
    Real.contDiff_exp.contMDiff.comp hpotential.neg

/-- Tangent-action chain rule for `e^{-f}`. -/
theorem tangentSectionAction_expNeg
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) (x : M) :
    RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
        (I := I) X (expNegPotentialDensity potential) x =
      -expNegPotentialDensity potential x *
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
          (I := I) X potential x := by
  have hmf :=
    RicciFlower.Analysis.DivergenceTheorem.mfderiv_exp_neg_toLinearMap
      (I := I) (f := potential) (x := x)
      (hpotential.mdifferentiableAt (by simp))
  unfold RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
    expNegPotentialDensity
  change
    extDerivFun (I := I) (fun y : M => Real.exp (-(potential y))) x (X x) =
      -Real.exp (-(potential x)) *
        extDerivFun (I := I) potential x (X x)
  rw [extDerivFun, extDerivFun]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply]
  have happly := congrArg (fun L => L (X x)) hmf
  simpa [smul_eq_mul] using happly

/-- The global divergence field used to cancel the connection-variation term in
formula 5.10, once the metric trace of the connection variation has already
been constructed as a smooth tangent section.  If `traceVec = tr_g A`, then
this is the book's vector field `X = e^{-f} tr_g A`. -/
def connTraceVec
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
  RicciFlower.Analysis.DivergenceTheorem.smoothSmul
    (I := I) (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec

/-- Divergence of `connTraceVec`.  This is the global smooth-section version of
`div(e^{-f} tr_g A) = e^{-f}(div(tr_g A) - tr_g A(f))`. -/
theorem connTraceDivEq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∀ x : M,
      RicciFlower.Analysis.DivergenceTheorem.divergence_g
          (I := I) g
          (connTraceVec (I := I) hpotential traceVec) x =
        expNegPotentialDensity potential x * weightedDivergenceTrace x := by
  intro x
  rw [connTraceVec]
  rw [RicciFlower.Analysis.DivergenceTheorem.divergence_g_smoothSmul
    (I := I) g (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec x]
  rw [hdivTrace x]
  rw [tangentSectionAction_expNeg (I := I) traceVec hpotential x]
  rw [hactionTrace x, hweighted x]
  ring

/-- Closed weighted-divergence cancellation when the divergence field is the
actual section `connTraceVec = e^{-f} tr_g A`. -/
theorem weightedDivZero_of_connTrace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  exact weightedDivZero (I := I) g
    (connTraceVec (I := I) hpotential traceVec) hmeas
    (connTraceDivEq (I := I) g hpotential traceVec hdivTrace
      hactionTrace hweighted)

/-- Weighted Green in the exact scalar form used by formula 5.10 for the
shifted Hessian trace `Delta(h - V/2)`. -/
theorem shiftIntEq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q shiftedTrace potentialVariation metricVariationTrace :
      M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x -
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  calc
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          RicciFlower.Analysis.DivergenceTheorem.Δ_g (I := I) g hq x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = ∫ x,
        q x *
          (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x +
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      exact weightedGreen (I := I) g hpotential hq hmeas
    _ = ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x -
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      dsimp
      rw [hqeq x]
      unfold expWeightedMeasureVariationFactor
      ring

/-- Moving-volume derivative for integrals against `e^{-f_s} dmu_s`. -/
theorem expWeightedMeasureIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {potentialPath phiPath : Real -> M -> Real}
    {s0 : Real}
    {potentialVariation metricVariationTrace phiVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (hphi_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => phiPath s x)
          (phiVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x * phiPath s x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (phiPath s0) phiVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  have hvol :=
    volume_variation_formula_clean_at
      (I := I) (M := M) G
      (f := fun s : Real => fun x : M =>
        expNegPotentialDensity (potentialPath s) x * phiPath s x)
      (t₀ := s0) hmetric_reg hintegrand_reg
  refine hvol.congr_deriv ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hdens :=
    expNegPotentialDensity_hasDerivAt
      (M := M) (potentialPath := potentialPath)
      (potentialVariation := potentialVariation)
      hpotential_deriv x
  have hprod :
      HasDerivAt
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        (-(potentialVariation x) *
            expNegPotentialDensity (potentialPath s0) x * phiPath s0 x +
          expNegPotentialDensity (potentialPath s0) x * phiVariation x)
        s0 :=
    hdens.mul (hphi_deriv x)
  have hderiv := hprod.deriv
  change
    deriv
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0 +
      1 / 2 * traceTimeDerivMetricAt (I := I) G s0 x *
        (expNegPotentialDensity (potentialPath s0) x * phiPath s0 x) =
    expWeightedIntegralVariationIntegrand
      (potentialPath s0) potentialVariation metricVariationTrace
      (phiPath s0) phiVariation x
  rw [hderiv, htrace x]
  unfold expWeightedIntegralVariationIntegrand
    expWeightedMeasureVariationFactor
  ring

/-- Scalar derivative of the bracket `R + |grad f|^2`. -/
def fFunctionalBracketVariation
    (scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + gradPotentialNormSqVariation x

theorem fFunctionalBracket_hasDerivAt
    {scalarCurvaturePath gradPotentialNormSqPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x)
      (fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hgrad_deriv x)
  simpa [fFunctionalBracket, fFunctionalBracketVariation] using h

/-- Scalar derivative of the closed bracket `R + Delta f`. -/
theorem closedBracket_deriv
    {scalarCurvaturePath lapPotentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalClosedBracket (scalarCurvaturePath s)
          (lapPotentialPath s) x)
      (fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hlap_deriv x)
  simpa [fFunctionalClosedBracket, fFunctionalClosedBracketVariation] using h

/-- Formula specialized to Perelman's `F` bracket.  The derivatives of scalar
curvature and `|grad f|^2` are scalar inputs; formula 5.10 later identifies
their integrated geometric expression. -/
theorem fFunctionalBaseIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalBracket (scalarCurvaturePath s)
        (gradPotentialNormSqPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation)
    hpotential_deriv
    (fFunctionalBracket_hasDerivAt
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (gradPotentialNormSqVariation := gradPotentialNormSqVariation)
      hscalar_deriv hgrad_deriv)
    htrace hmetric_reg hintegrand_reg

/-- Moving-volume first derivative for the closed bracket `R + Delta f`.
This is the derivative producer used before comparing the closed bracket with
the original `R + |grad f|^2` form by weighted integration by parts. -/
theorem closedBase_deriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalClosedBracket (scalarCurvaturePath s0)
            (lapPotentialPath s0))
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalClosedBracket (scalarCurvaturePath s)
        (lapPotentialPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation)
    hpotential_deriv
    (closedBracket_deriv
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (lapPotentialPath := lapPotentialPath) (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (lapPotentialVariation := lapPotentialVariation)
      hscalar_deriv hlap_deriv)
    htrace hmetric_reg hintegrand_reg

/-- Convert a base-integral derivative into the path-level first-variation
predicate for `F`. -/
theorem FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 firstVariation : Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (muPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(muPath s))
    (hbase :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(muPath s))
        firstVariation s0) :
    FFunctionalHasFirstVariationAt muPath scalarCurvaturePath
      gradPotentialNormSqPath potentialPath s0 firstVariation := by
  unfold FFunctionalHasFirstVariationAt fFunctionalAlong
  exact hbase.congr_of_eventuallyEq hbase_eq

/-- First-variation producer for `F` from moving-volume differentiation. -/
theorem FFunctionalHasFirstVariationAt_of_volumeVariation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (volumeMeasureFamily (I := I) (M := M) G s)
          (scalarCurvaturePath s) (gradPotentialNormSqPath s)
          (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    FFunctionalHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G)
      scalarCurvaturePath gradPotentialNormSqPath potentialPath s0
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) := by
  exact FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    hbase_eq
    (fFunctionalBaseIntegral_hasDerivAt_at
      (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_reg
      hintegrand_reg)

end Geometry

/-! ## Formula 5.10 proof-step interfaces -/

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

section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Integral bridge from the moving-volume first-variation integrand to the
pre-cancellation formula 5.10 integral.

This is the exact `hfirst` shape consumed by the component-level formula 5.10
assembly theorem once the geometric variation producer has identified
`delta(R + |grad f|^2)`. -/
theorem firstVariationIntegral_eq_pre510
    [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      gradPotentialNormSqVariation : M -> Real}
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hgrad0 : gradPotentialNormSqPath s0 = gradPotentialNormSq)
    (hpotential0 : potentialPath s0 = potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hvariation :
      ∀ x : M,
        fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x +
            (lapPotential x - gradPotentialNormSq x) *
              expWeightedMeasureVariationFactor potentialVariation
                metricVariationTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  calc
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        =
      ∫ x,
        expNegPotentialDensity potential x *
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) := by
      simp only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, hscalar0, hgrad0, hpotential0]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (expWeightedIntegralVariation_eq_pre510 (M := M)
          (hvariation := hvariation))
    _ =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
      exact (expNegPotentialWeightedMeasure_integral_eq_base
        (mu := riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
        (potential := potential)
        (integrand :=
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace)
        hmeas).symm

/-- Closed-bracket integral bridge for formula 5.10.

This is the producer form suited to the `R + Delta f` trace variation coming
from `LeviCivita.Variation`: once the closed bracket varies by
`-v^{ij}(Ric_ij + Hess_ij f) + div_A + Hess(h - V/2)`, the moving-volume
integrand is exactly the pre-cancellation formula 5.10 integral. -/
theorem closedIntegral_eq_pre510
    [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace closedBracketVariation : M -> Real}
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hvariation :
      ∀ x : M,
        closedBracketVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  calc
    (∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        =
      ∫ x,
        expNegPotentialDensity potential x *
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) := by
      simp only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (expWeightedClosedVariation_eq_pre510 (M := M)
          (hvariation := hvariation))
    _ =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
      exact (expNegPotentialWeightedMeasure_integral_eq_base
        (mu := riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
        (potential := potential)
        (integrand :=
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace)
        hmeas).symm

/-- Integral bridge from the original `R + |grad f|^2` moving-volume integrand
to the pre-cancellation formula 5.10 integral via the closed bracket
`R + Delta f`.  The hypothesis `hclosed_compare` is the differentiated
closed-manifold Green/IBP comparison between the two bracket forms. -/
theorem firstVar_pre510_closed
    [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      gradPotentialNormSqVariation closedBracketVariation : M -> Real}
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hclosed_compare :
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
    (hclosed_variation :
      ∀ x : M,
        closedBracketVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  rw [hclosed_compare]
  exact closedIntegral_eq_pre510 (I := I) (M := M) G hmeas hclosed_variation

/-- Convert a per-time weighted-IBP equality into equality of the base-measure
integrals used by the moving-volume derivative theorem. -/
theorem bracketClosed_eventually
    {muPath : Real -> Measure M}
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    (hmeas :
      ∀ᶠ s in nhds s0,
        AEMeasurable
          (fun x : M =>
            ENNReal.ofReal (expNegPotentialDensity (potentialPath s) x))
          (muPath s))
    (hibp :
      ∀ᶠ s in nhds s0,
        (∫ x,
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
          ∂(expNegPotentialWeightedMeasure (muPath s)
              (potentialPath s))) =
        ∫ x,
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
          ∂(expNegPotentialWeightedMeasure (muPath s)
              (potentialPath s))) :
    (fun s : Real =>
      ∫ x,
        expNegPotentialDensity (potentialPath s) x *
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
        ∂(muPath s)) =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x
          ∂(muPath s) := by
  filter_upwards [hmeas, hibp] with s hmeas_s hibp_s
  calc
    (∫ x,
      expNegPotentialDensity (potentialPath s) x *
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x
      ∂(muPath s))
        =
      ∫ x,
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x
        ∂(expNegPotentialWeightedMeasure (muPath s)
            (potentialPath s)) := by
        exact (expNegPotentialWeightedMeasure_integral_eq_base
          (mu := muPath s) (potential := potentialPath s)
          (integrand :=
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s)) hmeas_s).symm
    _ =
      ∫ x,
        fFunctionalClosedBracket (scalarCurvaturePath s)
          (lapPotentialPath s) x
        ∂(expNegPotentialWeightedMeasure (muPath s)
            (potentialPath s)) := hibp_s
    _ =
      ∫ x,
        expNegPotentialDensity (potentialPath s) x *
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
        ∂(muPath s) := by
        exact expNegPotentialWeightedMeasure_integral_eq_base
          (mu := muPath s) (potential := potentialPath s)
          (integrand :=
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s)) hmeas_s

/-- Derivative comparison between the original `R + |grad f|^2` bracket and
the closed `R + Delta f` bracket.  The input equality is the per-time weighted
IBP identity, already transported to the base-measure integral shape. -/
theorem closedCompare
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential potential
      scalarCurvatureVariation lapPotentialVariation
      gradPotentialNormSqVariation potentialVariation metricVariationTrace :
      M -> Real}
    (hbase_eq :
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) =ᶠ[nhds s0]
        fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalClosedBracket (scalarCurvaturePath s)
                (lapPotentialPath s) x
            ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0) := by
  have horig :=
    fFunctionalBaseIntegral_hasDerivAt_at (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_reg horig_reg
  have hclosed :=
    closedBase_deriv (I := I) (M := M) G
      hscalar_deriv hlap_deriv hpotential_deriv htrace hmetric_reg
      hclosed_reg
  have hclosed_orig :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(volumeMeasureFamily (I := I) (M := M) G s))
        (∫ x,
          expWeightedIntegralVariationIntegrand
            (potentialPath s0) potentialVariation metricVariationTrace
            (fFunctionalClosedBracket (scalarCurvaturePath s0)
              (lapPotentialPath s0))
            (fFunctionalClosedBracketVariation scalarCurvatureVariation
              lapPotentialVariation) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        s0 :=
    hclosed.congr_of_eventuallyEq hbase_eq
  have hderiv_eq := horig.unique hclosed_orig
  calc
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        =
      ∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalClosedBracket (scalarCurvaturePath s0)
            (lapPotentialPath s0))
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0) := hderiv_eq
    _ =
      ∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0) := by
        simp [hpotential0, hscalar0, hlap0]

/-- Formula 5.10 pre-cancellation integral with the closed-bracket comparison
supplied by the derivative of the per-time weighted IBP identity. -/
theorem firstVar_pre510_weighted
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      lapPotentialVariation gradPotentialNormSqVariation : M -> Real}
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hbase_eq :
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) =ᶠ[nhds s0]
        fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalClosedBracket (scalarCurvaturePath s)
                (lapPotentialPath s) x
            ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential)
    (hclosed_variation :
      ∀ x : M,
        fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  apply firstVar_pre510_closed (I := I) (M := M) G hmeas
  · exact closedCompare (I := I) (M := M) G hbase_eq
      hscalar_deriv hgrad_deriv hlap_deriv hpotential_deriv htrace
      hmetric_reg horig_reg hclosed_reg hpotential0 hscalar0 hlap0
  · exact hclosed_variation

/-- Formula 5.10 pre-cancellation integral with the closed-bracket comparison
supplied in the natural weighted-measure form:
`∫ (R + |grad f|^2)e^{-f}dmu = ∫ (R + Delta f)e^{-f}dmu` near the base time. -/
theorem firstVar_pre510_ibp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      lapPotentialVariation gradPotentialNormSqVariation : M -> Real}
    (hmeas0 :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hmeas_near :
      ∀ᶠ s in nhds s0,
        AEMeasurable
          (fun x : M =>
            ENNReal.ofReal (expNegPotentialDensity (potentialPath s) x))
          (volumeMeasureFamily (I := I) (M := M) G s))
    (hibp_near :
      ∀ᶠ s in nhds s0,
        (∫ x,
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s))) =
        ∫ x,
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s)))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential)
    (hclosed_variation :
      ∀ x : M,
        fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  apply firstVar_pre510_weighted (I := I) (M := M) G hmeas0
  · exact bracketClosed_eventually
      (M := M)
      (muPath := volumeMeasureFamily (I := I) (M := M) G)
      (scalarCurvaturePath := scalarCurvaturePath)
      (lapPotentialPath := lapPotentialPath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (potentialPath := potentialPath)
      (s0 := s0)
      hmeas_near hibp_near
  · exact hscalar_deriv
  · exact hgrad_deriv
  · exact hlap_deriv
  · exact hpotential_deriv
  · exact htrace
  · exact hmetric_reg
  · exact horig_reg
  · exact hclosed_reg
  · exact hpotential0
  · exact hscalar0
  · exact hlap0
  · exact hclosed_variation

/-- Formula 5.10 from the geometric connection-trace divergence field and the
weighted Green shift identity.  This is the assembly form matching the book's
step where `∇_p(e^{-f} g^{ij} A^p_{ij})` integrates to zero. -/
theorem formula510_of_connTrace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hdiv_zero :
      ∫ x, weightedDivergenceTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 :=
    weightedDivZero_of_connTrace (I := I) g hpotential traceVec hmeas
      hdivTrace hactionTrace hweighted
  have hshift_eq :
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x -
              g.inner x
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) :=
    shiftIntEq (I := I) g hpotential hq hmeas hshift hqeq
  have hshift_final :
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
    calc
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x -
              g.inner x
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := hshift_eq
      _ = ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro x
        simp [hlap x, hgradSq x]
  exact formula510_of_ints
    (weightedMeasure :=
      expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
    hfirst hfinal_int hdiv_int hshift_int hcorr_int hdiv_zero hshift_final

/-- Coordinate-frame action formula for the constructed connection-trace field.
This is the first local realization needed to identify the book's
`g^{ij} A^p_{ij} ∂_p f` term with the intrinsic tangent-section action. -/
theorem connTraceAction_coord
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
        (I := I) (RicciFlower.Realized.connTraceField (I := I) g A)
        potential x =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ x) *
              componentRS (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
                (A x) (fun _ : Fin 1 => p)
                (fun q : Fin 2 => if q = 0 then i else j)) *
          extDerivFun (I := I) potential x
            (coordinateFrameAt (I := I) x₀ p x) := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    RicciFlower.Realized.connTraceField (I := I) g A
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  have hX :
      X x = ∑ p : CoordinateIdx (𝕜 := Real) E,
        hframe.coeff p x (X x) • frame p x := by
    simpa [X, frame, hframe] using hframe.coeff_sum_eq (fun y : M => X y) hx
  rw [RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction_def]
  rw [← RicciFlower.extDerivFun_real_eq_mfderiv I potential x (X x)]
  change extDerivFun (I := I) potential x (X x) = _
  rw [hX, map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [map_smul]
  have hcoeff :=
    RicciFlower.Realized.connTraceField_coord (I := I) g A x₀ hx p
  rw [hcoeff]
  exact smul_eq_mul ..

/-- Intrinsic raw divergence trace of the constructed field `tr_g A`. -/
def connTraceRawDiv
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2) : M -> Real :=
  fun x =>
    RicciFlower.Analysis.DivergenceTheorem.divergence_g
      (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x

/-- Pointwise coordinate-centered action trace of `tr_g A` on a scalar
potential.  The chart is centered at the point being evaluated, so this is a
global scalar function without choosing a fixed chart. -/
def connTraceAction
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real) : M -> Real :=
  fun x =>
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        extDerivFun (I := I) potential x
          (coordinateFrameAt (I := I) x p x)

/-- Coordinate action trace written directly from Christoffel-variation
components and potential-gradient components.  The finite-sum order matches
`connTraceAction`, so the bridge is only component substitution. -/
def gammaActionTrace
    (g : SmoothRiemannianMetric I M)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real) :
    M -> Real :=
  fun x =>
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            christoffelVariation x p i j) *
        gradPotential x p

/-- The raw scalar trace of `nabla_p A^p_ij`, contracted with the inverse
metric in the point-centered coordinate frame. -/
def gammaRawDivergenceTrace
    (g : SmoothRiemannianMetric I M)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real) :
    M -> Real :=
  fun x =>
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            nablaChristoffelVariation x p p i j)

private theorem rawDivTraceAlg
    {Idx : Type*} [Fintype Idx]
    (U : Idx -> Idx -> Real)
    (dU : Idx -> Idx -> Idx -> Real)
    (A : Idx -> Idx -> Idx -> Real)
    (dA nablaA : Idx -> Idx -> Idx -> Idx -> Real)
    (Gamma : Idx -> Idx -> Idx -> Real)
    (hUtrace : ∀ d : Idx,
      (∑ i : Idx, ∑ j : Idx, dU d i j * A d i j) =
        -∑ i : Idx, ∑ j : Idx, U i j *
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a)))
    (hAtrace : ∀ i j : Idx,
      (∑ d : Idx, nablaA d d i j) =
        (∑ d : Idx, dA d d i j) +
          (∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a)) -
          (∑ d : Idx,
            ((∑ a : Idx, Gamma d i a * A d a j) +
             (∑ a : Idx, Gamma d j a * A d i a)))) :
    (∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
        (dU d i j * A d i j + U i j * dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a)) =
      ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, nablaA d d i j) := by
  classical
  calc
    (∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
        (dU d i j * A d i j + U i j * dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a))
        =
      (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, dU d i j * A d i j) +
      (∑ i : Idx, ∑ j : Idx, U i j *
        (∑ d : Idx, dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a)) := by
          simp only [Finset.sum_add_distrib]
          congr 2
          calc
            (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * dA d d i j)
                =
              ∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * dA d d i j := by
              calc
                (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * dA d d i j)
                    =
                  ∑ i : Idx, ∑ d : Idx, ∑ j : Idx, U i j * dA d d i j := by
                  rw [Finset.sum_comm]
                _ =
                  ∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * dA d d i j := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
    _ =
      (∑ d : Idx,
        -∑ i : Idx, ∑ j : Idx, U i j *
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) +
      (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a)) := by
        rw [show
          (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, dU d i j * A d i j) =
            ∑ d : Idx,
              -∑ i : Idx, ∑ j : Idx, U i j *
                ((∑ a : Idx, Gamma d i a * A d a j) +
                 (∑ a : Idx, Gamma d j a * A d i a)) by
          refine Finset.sum_congr rfl fun d _ => hUtrace d]
     _ =
      ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, nablaA d d i j) := by
        let L : Idx -> Idx -> Idx -> Real := fun d i j =>
          (∑ a : Idx, Gamma d i a * A d a j) +
            (∑ a : Idx, Gamma d j a * A d i a)
        let T : Idx -> Real := fun d => ∑ a : Idx, Gamma d a a
        have hneg :
            (∑ d : Idx, -∑ i : Idx, ∑ j : Idx, U i j * L d i j) =
              -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) := by
          calc
            (∑ d : Idx, -∑ i : Idx, ∑ j : Idx, U i j * L d i j)
                =
              -∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * L d i j := by
              rw [Finset.sum_neg_distrib]
            _ =
              -∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * L d i j := by
              congr 1
              calc
                (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * L d i j)
                    =
                  ∑ i : Idx, ∑ d : Idx, ∑ j : Idx, U i j * L d i j := by
                  rw [Finset.sum_comm]
                _ =
                  ∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * L d i j := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) := by
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
        have hden :
            (∑ d : Idx,
              (∑ i : Idx, ∑ j : Idx, U i j * A d i j) * T d) =
              ∑ i : Idx, ∑ j : Idx,
                U i j * (∑ d : Idx, A d i j * T d) := by
          calc
            (∑ d : Idx,
              (∑ i : Idx, ∑ j : Idx, U i j * A d i j) * T d)
                =
              ∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
                U i j * A d i j * T d := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_mul]
            _ =
              ∑ i : Idx, ∑ j : Idx, ∑ d : Idx,
                U i j * A d i j * T d := by
              calc
                (∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
                  U i j * A d i j * T d)
                    =
                  ∑ i : Idx, ∑ d : Idx, ∑ j : Idx,
                    U i j * A d i j * T d := by
                  rw [Finset.sum_comm]
                _ =
                  ∑ i : Idx, ∑ j : Idx, ∑ d : Idx,
                    U i j * A d i j * T d := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ i : Idx, ∑ j : Idx,
                U i j * (∑ d : Idx, A d i j * T d) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
        calc
          (∑ d : Idx, -∑ i : Idx, ∑ j : Idx, U i j *
                ((∑ a : Idx, Gamma d i a * A d a j) +
                 (∑ a : Idx, Gamma d j a * A d i a))) +
              (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
            (∑ d : Idx,
              (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
                (∑ a : Idx, Gamma d a a))
              =
            -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) +
              (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
            (∑ i : Idx, ∑ j : Idx,
              U i j * (∑ d : Idx, A d i j * T d)) := by
              simp only [L, T]
              rw [hneg, hden]
          _ =
            ∑ i : Idx, ∑ j : Idx, U i j *
              ((∑ d : Idx, dA d d i j) +
                (∑ d : Idx, A d i j * T d) -
                (∑ d : Idx, L d i j)) := by
              calc
                -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) +
                    (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
                  (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, A d i j * T d))
                    =
                  ∑ i : Idx, ∑ j : Idx,
                    (-(U i j * (∑ d : Idx, L d i j)) +
                      U i j * (∑ d : Idx, dA d d i j) +
                      U i j * (∑ d : Idx, A d i j * T d)) := by
                    simp [Finset.sum_add_distrib, Finset.sum_neg_distrib]
                _ =
                  ∑ i : Idx, ∑ j : Idx, U i j *
                    ((∑ d : Idx, dA d d i j) +
                      (∑ d : Idx, A d i j * T d) -
                      (∑ d : Idx, L d i j)) := by
                    refine Finset.sum_congr rfl fun i _ => ?_
                    refine Finset.sum_congr rfl fun j _ => ?_
                    ring
          _ =
            ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, nablaA d d i j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hAtrace i j]

private theorem traceUpperAlg
    {Idx : Type*} [Fintype Idx]
    (A : Idx -> Idx -> Idx -> Real)
    (Gamma : Idx -> Idx -> Idx -> Real)
    (hGamma : ∀ d a k : Idx, Gamma d a k = Gamma a d k)
    (i j : Idx) :
    (∑ d : Idx, ∑ a : Idx, Gamma d a d * A a i j) =
      ∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a) := by
  classical
  calc
    (∑ d : Idx, ∑ a : Idx, Gamma d a d * A a i j)
        =
      ∑ a : Idx, ∑ d : Idx, Gamma d a d * A a i j := by
      rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ d : Idx, Gamma a d d * A a i j := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hGamma d a d]
    _ =
      ∑ a : Idx, A a i j * (∑ d : Idx, Gamma a d d) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    _ =
      ∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a) := rfl

private theorem traceNablaAlg
    {Idx : Type*} [Fintype Idx]
    (A : Idx -> Idx -> Idx -> Real)
    (dA nablaA : Idx -> Idx -> Idx -> Idx -> Real)
    (Gamma : Idx -> Idx -> Idx -> Real)
    (hA : ∀ d k i j : Idx,
      nablaA d k i j =
        dA d k i j +
          (∑ a : Idx, Gamma d a k * A a i j) -
          (∑ a : Idx, Gamma d i a * A k a j) -
          (∑ a : Idx, Gamma d j a * A k i a))
    (hGamma : ∀ d a k : Idx, Gamma d a k = Gamma a d k)
    (i j : Idx) :
    (∑ d : Idx, nablaA d d i j) =
      (∑ d : Idx, dA d d i j) +
        (∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a)) -
        (∑ d : Idx,
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) := by
  classical
  calc
    (∑ d : Idx, nablaA d d i j)
        =
      ∑ d : Idx,
        (dA d d i j +
          (∑ a : Idx, Gamma d a d * A a i j) -
          (∑ a : Idx, Gamma d i a * A d a j) -
          (∑ a : Idx, Gamma d j a * A d i a)) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hA d d i j]
    _ =
      (∑ d : Idx, dA d d i j) +
        (∑ d : Idx, ∑ a : Idx, Gamma d a d * A a i j) -
        (∑ d : Idx,
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    _ =
      (∑ d : Idx, dA d d i j) +
        (∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a)) -
        (∑ d : Idx,
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) := by
      rw [traceUpperAlg A Gamma hGamma i j]

/-- Scalar contraction of the weighted Christoffel-divergence tensor
`nabla_p A^p_ij - A^p_ij partial_p f`. -/
def christoffelWeightedDivergenceTrace
    (g : SmoothRiemannianMetric I M)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real) :
    M -> Real :=
  fun x =>
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          christoffelWeightedDivergenceInFrame nablaChristoffelVariation
            christoffelVariation gradPotential x i j

/-- The scalar contraction of
`nabla_p A^p_ij - A^p_ij partial_p f` is the raw divergence trace minus the
trace-field action term.  This is only finite-sum algebra; the geometric
frontier remains identifying `gammaRawDivergenceTrace` with
`divergence_g(tr_g A)`. -/
theorem weightedTrace_eq
    (g : SmoothRiemannianMetric I M)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real) :
    christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential =
      fun x =>
        gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x -
          gammaActionTrace (I := I) g christoffelVariation gradPotential x := by
  classical
  funext x
  unfold christoffelWeightedDivergenceTrace gammaRawDivergenceTrace
    gammaActionTrace christoffelWeightedDivergenceInFrame
  rw [show
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ p : CoordinateIdx (𝕜 := Real) E,
                nablaChristoffelVariation x p p i j) -
              ∑ p : CoordinateIdx (𝕜 := Real) E,
                christoffelVariation x p i j * gradPotential x p)) =
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              (∑ p : CoordinateIdx (𝕜 := Real) E,
                nablaChristoffelVariation x p p i j)) -
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x x) *
                (∑ p : CoordinateIdx (𝕜 := Real) E,
                  christoffelVariation x p i j * gradPotential x p)) by
      simp only [mul_sub, Finset.sum_sub_distrib]]
  congr 1
  calc
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            christoffelVariation x p i j * gradPotential x p))
        =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              christoffelVariation x p i j * gradPotential x p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              christoffelVariation x p i j * gradPotential x p := by
        calc
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              ∑ p : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j
                    (extChartAt I x x) *
                  christoffelVariation x p i j * gradPotential x p)
              =
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ p : CoordinateIdx (𝕜 := Real) E,
                ∑ j : CoordinateIdx (𝕜 := Real) E,
                  inverseMetricFlatModelInChart_component (I := I) g x i j
                      (extChartAt I x x) *
                    christoffelVariation x p i j * gradPotential x p := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
          _ =
            ∑ p : CoordinateIdx (𝕜 := Real) E,
              ∑ i : CoordinateIdx (𝕜 := Real) E,
                ∑ j : CoordinateIdx (𝕜 := Real) E,
                  inverseMetricFlatModelInChart_component (I := I) g x i j
                      (extChartAt I x x) *
                    christoffelVariation x p i j * gradPotential x p := by
              rw [Finset.sum_comm]
    _ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              christoffelVariation x p i j) *
          gradPotential x p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

/-- The coordinate-centered `connTraceAction` is the intrinsic tangent action
of the constructed field. -/
theorem connTraceAction_eq
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real) (x : M) :
    RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
        (I := I) (RicciFlower.Realized.connTraceField (I := I) g A)
        potential x =
      connTraceAction (I := I) g A potential x := by
  simpa [connTraceAction] using
    connTraceAction_coord (I := I) g A potential x
      (coordinateFrameAt_mem (I := I) x)

/-- Component bridge for the action term: once `A` realizes the Christoffel
variation tensor and `gradPotential` realizes the coordinate directional
derivatives of the potential, the intrinsic action trace is the corresponding
finite component contraction. -/
theorem connTraceAction_eq_gamma
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p) :
    connTraceAction (I := I) g A potential =
      gammaActionTrace (I := I) g christoffelVariation gradPotential := by
  funext x
  unfold connTraceAction gammaActionTrace
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [hgrad x p]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hA x p i j]

/-- Once the raw divergence of `tr_g A` has been identified with
`gammaRawDivergenceTrace`, the weighted scalar trace is automatically
`div(tr_g A) - (tr_g A)(f)`. -/
theorem weightedTrace_of_raw
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hraw :
      ∀ x : M,
        connTraceRawDiv (I := I) g A x =
          gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x)
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p) :
    ∀ x : M,
      christoffelWeightedDivergenceTrace (I := I) g
          nablaChristoffelVariation christoffelVariation gradPotential x =
        connTraceRawDiv (I := I) g A x -
          connTraceAction (I := I) g A potential x := by
  intro x
  have hweighted :=
    congrFun
      (weightedTrace_eq (I := I) g nablaChristoffelVariation
        christoffelVariation gradPotential) x
  have haction :=
    congrFun
      (connTraceAction_eq_gamma (I := I) g A potential
        christoffelVariation gradPotential hA hgrad) x
  calc
    christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential x =
      gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x -
        gammaActionTrace (I := I) g christoffelVariation gradPotential x := hweighted
    _ = connTraceRawDiv (I := I) g A x -
          connTraceAction (I := I) g A potential x := by
        rw [← hraw x, ← haction]

/-- On the coordinate-frame domain, the divergence theorem's chart coefficient
is the same coefficient as the `coordinateFrameAt` local-frame coefficient. -/
private theorem chartCoeff_eq_coordinateFrame_coeff
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀ X p x =
      (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x (X x) := by
  classical
  let e := coordinateTrivializationAt (I := I) x₀
  let b : Module.Basis (CoordinateIdx (𝕜 := Real) E) Real E := Module.finBasis Real E
  have hxE : x ∈ e.baseSet := by
    simpa [e, coordinateFrameSet] using hx
  have hcoeff :=
    Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
      (I := I) (e := e) (b := b) (x := x) hxE
      (fun y : M => X y) p
  have hchart :=
    Bundle.Trivialization.localFrame_coeff_eq_coeff
      (I := I) (e := e) (b := b) (s := fun y : M => X y)
      (x := x) (i := p) hxE
  have hbasis :
      (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx =
        e.basisAt b hxE := by
    ext j
    rw [IsLocalFrameOn.toBasisAt_coe]
    simpa [e, b, coordinateFrameAt] using
      (Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := j) hxE)
  rw [(coordinateFrameAt_isLocalFrame (I := I) x₀).coeff_apply_of_mem
    hx (fun y : M => X y) p]
  rw [hbasis]
  rw [← hcoeff]
  simpa [RicciFlower.Analysis.DivergenceTheorem.chartCoeff, e, b] using hchart.symm

/-- Local coordinate expression for the chart coefficient of the constructed
trace field.  This is the coefficient bridge needed before differentiating the
Voss-Weyl divergence formula. -/
theorem connTraceChartCoeff_eventually
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p y)
      =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              (A y
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) y))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
  classical
  have hcoeff :=
    RicciFlower.Realized.connTraceCoeff_eventually (I := I) g A x₀ p
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀), hcoeff] with y hy hcoeff_y
  rw [chartCoeff_eq_coordinateFrame_coeff
    (I := I) (RicciFlower.Realized.connTraceField (I := I) g A)
    x₀ hy p]
  exact hcoeff_y

/-- Model-chart version of `connTraceChartCoeff_eventually`.

This is the bridge needed before differentiating the Voss-Weyl expression:
near the chart center, the pulled-back chart coefficient of `tr_g A` is the
finite inverse-metric contraction of the pulled-back `(1,2)` tensor
components. -/
theorem connTraceChartCoeffOnE_eventually
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : E =>
        RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p y)
      =ᶠ[nhds (extChartAt I x₀ x₀)]
      fun y : E =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j y *
              (A ((extChartAt I x₀).symm y)
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) ((extChartAt I x₀).symm y)))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j)
                    ((extChartAt I x₀).symm y)) := by
  classical
  have hM := connTraceChartCoeff_eventually (I := I) g A x₀ p
  let z₀ : E := extChartAt I x₀ x₀
  have hsymm_tend :
      Filter.Tendsto (fun z : E => (extChartAt I x₀).symm z) (nhds z₀) (nhds x₀) := by
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
      (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
    simpa only [ContinuousAt, z₀, hleft, Function.comp_def] using
      continuousAt_extChartAt_symm (I := I) x₀
  have hcomp := hM.comp_tendsto hsymm_tend
  filter_upwards [hcomp, extChartAt_target_mem_nhds' (I := I)
      (x := x₀) (y := z₀) (by simp [z₀])] with y hcoeff hy_target
  have hright : extChartAt I x₀ ((extChartAt I x₀).symm y) = y :=
    (extChartAt I x₀).right_inv hy_target
  have hcoeff' :
      RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p
          ((extChartAt I x₀).symm y) =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ ((extChartAt I x₀).symm y)) *
              (A ((extChartAt I x₀).symm y)
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) ((extChartAt I x₀).symm y)))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j)
                    ((extChartAt I x₀).symm y)) := by
    simpa [Function.comp_def] using hcoeff
  rw [show
      RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p y =
        RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p
          ((extChartAt I x₀).symm y) by rfl]
  rw [hcoeff']
  rw [hright]

/-- Partial-derivative form of `connTraceChartCoeffOnE_eventually`.

This lets the Voss-Weyl raw divergence formula differentiate the explicit
inverse-metric contraction instead of the abstract chart coefficient. -/
theorem connTraceChartCoeff_partial
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x
          (RicciFlower.Realized.connTraceField (I := I) g A) p)
        (extChartAt I x x)
      =
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
      (fun y : E =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j y *
              (A ((extChartAt I x).symm y)
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x (if q = 0 then i else j)
                    ((extChartAt I x).symm y)))
      (extChartAt I x x) := by
  have h :=
    connTraceChartCoeffOnE_eventually (I := I) g A x p
  unfold RicciFlower.Analysis.DivergenceTheorem.partialDeriv
  rw [Filter.EventuallyEq.fderiv_eq h]

/-- Center value of the chart coefficient of `tr_g A` in the point-centered
coordinate frame. -/
theorem connTraceChartCoeff_center
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x
        (RicciFlower.Realized.connTraceField (I := I) g A) p
        (extChartAt I x x)
      =
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  have hcoeff :=
    connTraceChartCoeff_eventually (I := I) g A x p
  have hcenter := hcoeff.eq_of_nhds
  have hsymm : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hxmem : x ∈ coordinateFrameSet (I := I) x :=
    coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have hconst :
      Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 x
          ((continuousMultilinearMap_basis
            (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
            (fun _ : Fin 1 => p)) x =
        basisTensor0S (I := I)
          (coordinateFrameAt_basis (I := I) x hxmem)
          (fun _ : Fin 1 => p) := by
    simpa using
      (RicciFlower.Coordinates.constInChart_basisTensor0S_coordFrame
        (𝕜 := Real) (I := I) (x₀ := x) (x := x) hxmem
        (fun _ : Fin 1 => p))
  calc
    RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x
        (RicciFlower.Realized.connTraceField (I := I) g A) p
        (extChartAt I x x)
        =
      RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x
        (RicciFlower.Realized.connTraceField (I := I) g A) p x := by
        simp [RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE]
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            (A x
              (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M) 1 x
                ((continuousMultilinearMap_basis
                  (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                  (fun _ : Fin 1 => p)) x))
              (fun q : Fin 2 =>
                coordinateFrameAt (I := I) x (if q = 0 then i else j) x) := hcenter
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x hxmem)
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [componentRS]
        simp [hconst, component0S, coordinateFrameAt_basis_apply]

/-- Voss-Weyl expansion of the raw divergence of the constructed trace field.
The remaining formula 5.10 geometric work is to rewrite this expression into
the Levi-Civita covariant trace of the connection-variation tensor. -/
theorem connTraceRawDiv_voss
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceRawDiv (I := I) g A x =
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
            (fun y : E =>
              RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE
                  (I := I) x
                  (RicciFlower.Realized.connTraceField (I := I) g A) p y *
                RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
                  (I := I) g x y)
            (extChartAt I x x)) /
        RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
  rfl

/-- Product-rule expansion of the raw divergence of the constructed trace
field.  This is the next normalization after the Voss-Weyl chart expression:
the raw divergence is split into a derivative of the trace-field coordinate
coefficient and the chart-density derivative correction. -/
theorem connTraceRawDiv_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceRawDiv (I := I) g A x =
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE
            (I := I) x (RicciFlower.Realized.connTraceField (I := I) g A) p)
          (extChartAt I x x)) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE
              (I := I) x (RicciFlower.Realized.connTraceField (I := I) g A) p
              (extChartAt I x x) *
            RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
              (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
                (I := I) g x) (extChartAt I x x)) /
          RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
  simpa [connTraceRawDiv] using
    RicciFlower.Analysis.DivergenceTheorem.divergence_g_chart_product
      (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x

/-- Voss-Weyl product expansion with the constructed trace field's chart
coefficients replaced by the explicit finite contraction
`g^{ij} A^p_ij`.

The remaining conversion to `gammaRawDivergenceTrace` is the standard
Levi-Civita coordinate-divergence algebra: combine the density derivative with
the Christoffel trace and use `∇g^{-1}=0`. -/
theorem connTraceRawDiv_chart_explicit
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceRawDiv (I := I) g A x =
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (fun y : E =>
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j y *
                  (A ((extChartAt I x).symm y)
                    (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                      (I := I) (M := M) 1 x
                      ((continuousMultilinearMap_basis
                        (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                        (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                    (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x (if q = 0 then i else j)
                        ((extChartAt I x).symm y)))
          (extChartAt I x x)) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x x) *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => p)
                  (fun q : Fin 2 => if q = 0 then i else j)) *
            RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
              (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
                (I := I) g x) (extChartAt I x x)) /
          RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
  classical
  rw [connTraceRawDiv_chart_product (I := I) g A x]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    exact connTraceChartCoeff_partial (I := I) g A x p
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [connTraceChartCoeff_center (I := I) g A x p]

private theorem partialDeriv_sum_mul2
    (U :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        E -> Real)
    (B :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> E -> Real)
    (dU :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (dB :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (y0 : E)
    (hUdiff : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real (U i j) y0)
    (hBdiff : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real (B p i j) y0)
    (hUderiv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (U i j) y0 = dU p i j)
    (hBderiv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (B p i j) y0 = dB p p i j) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              U i j y * B p i j y) y0) =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (dU p i j * B p i j y0 + U i j y0 * dB p p i j) := by
  classical
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold RicciFlower.Analysis.DivergenceTheorem.partialDeriv
  have hi :
      ∀ i ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
        DifferentiableAt Real
          (fun y : E =>
            ∑ j : CoordinateIdx (𝕜 := Real) E, U i j y * B p i j y) y0 := by
    intro i _
    exact DifferentiableAt.fun_sum fun j _ => (hUdiff i j).mul (hBdiff p i j)
  rw [fderiv_fun_sum hi]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj :
      ∀ j ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
        DifferentiableAt Real (fun y : E => U i j y * B p i j y) y0 := by
    intro j _
    exact (hUdiff i j).mul (hBdiff p i j)
  rw [fderiv_fun_sum hj]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_mul (hUdiff i j) (hBdiff p i j)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  have hU' :
      (fderiv Real (U i j) y0) ((Module.finBasis Real E) p) = dU p i j := by
    simpa [RicciFlower.Analysis.DivergenceTheorem.partialDeriv] using
      hUderiv p i j
  have hB' :
      (fderiv Real (B p i j) y0) ((Module.finBasis Real E) p) =
        dB p p i j := by
    simpa [RicciFlower.Analysis.DivergenceTheorem.partialDeriv] using
      hBderiv p i j
  rw [hU', hB']
  ring

/-- Product-rule producer for the derivative input consumed by
`connTraceRaw_eq_gamma`.

It expands the fixed-chart derivative of the explicit trace-field coefficient
`sum_i sum_j g^{ij} A^p_ij` into the inverse-metric derivative term plus the
component derivative of `A`. -/
theorem connTraceDeriv
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hgInvDiff : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x))
    (hADiff : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x))
    (hgInvDeriv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x) = gInvDeriv p i j)
    (hADeriv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x) = componentDeriv p p i j) :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (fun y : E =>
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j y *
                  (A ((extChartAt I x).symm y)
                    (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                      (I := I) (M := M) 1 x
                      ((continuousMultilinearMap_basis
                        (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                        (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                    (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x (if q = 0 then i else j)
                        ((extChartAt I x).symm y)))
          (extChartAt I x x)) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              (gInvDeriv p i j *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => p)
                    (fun q : Fin 2 => if q = 0 then i else j) +
                inverseMetricFlatModelInChart_component (I := I) g x i j
                    (extChartAt I x x) *
                  componentDeriv p p i j) := by
  classical
  let U :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        E -> Real := fun i j y =>
    inverseMetricFlatModelInChart_component (I := I) g x i j y
  let B :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> E -> Real := fun p i j y =>
    (A ((extChartAt I x).symm y)
      (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 x
        ((continuousMultilinearMap_basis
          (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
          (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
      (fun q : Fin 2 =>
        coordinateFrameAt (I := I) x (if q = 0 then i else j)
          ((extChartAt I x).symm y))
  have hprod :=
    partialDeriv_sum_mul2 (U := U) (B := B)
      (dU := gInvDeriv) (dB := componentDeriv)
      (y0 := extChartAt I x x)
      (by simpa [U] using hgInvDiff)
      (by simpa [B] using hADiff)
      (by simpa [U] using hgInvDeriv)
      (by simpa [B] using hADeriv)
  have hBcenter :
      ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        B p i j (extChartAt I x x) =
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
    intro p i j
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    have hsymm : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
    have hconst :
        Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 x
          ((continuousMultilinearMap_basis
            (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
            (fun _ : Fin 1 => p)) x =
          basisTensor0S (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (fun _ : Fin 1 => p) :=
      constInChart_basisTensor0S_coordFrame (𝕜 := Real) (I := I)
        (M := M) (r := 1) x (coordinateFrameAt_mem (I := I) x)
        (fun _ : Fin 1 => p)
    calc
      B p i j (extChartAt I x x) =
          (A ((extChartAt I x).symm (extChartAt I x x))
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm (extChartAt I x x))))
            (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x (if q = 0 then i else j)
            ((extChartAt I x).symm (extChartAt I x x))) := by
          rfl
      _ =
          (A x
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) x))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j) x) := by
          rw [hsymm]
      _ =
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
          rw [componentRS]
          simp [hconst, component0S, coordinateFrameAt_basis_apply]
  calc
    (∑ p : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x i j y *
                (A ((extChartAt I x).symm y)
                  (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                    (I := I) (M := M) 1 x
                    ((continuousMultilinearMap_basis
                      (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                      (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                  (fun q : Fin 2 =>
                    coordinateFrameAt (I := I) x (if q = 0 then i else j)
                      ((extChartAt I x).symm y)))
        (extChartAt I x x))
        =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (gInvDeriv p i j * B p i j (extChartAt I x x) +
              U i j (extChartAt I x x) * componentDeriv p p i j) := by
      simpa [U, B] using hprod
    _ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (gInvDeriv p i j *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => p)
                  (fun q : Fin 2 => if q = 0 then i else j) +
              inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x x) *
                componentDeriv p p i j) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hBcenter p i j]

/-- The density-derivative correction in the Voss-Weyl divergence formula is
the Christoffel trace correction for the Levi-Civita connection. -/
theorem connTraceDensityCorr
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
            (I := I) g x) (extChartAt I x x)) /
      RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
      =
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov
            (coordinateFrameAt (I := I) x)
            (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a) := by
  classical
  let C : CoordinateIdx (𝕜 := Real) E → Real := fun p =>
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j)
  let ρ : Real := RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
  let dρ : CoordinateIdx (𝕜 := Real) E → Real := fun p =>
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
      (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
        (I := I) g x) (extChartAt I x x)
  have htrace :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        dρ p / ρ =
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a := by
    intro p
    simpa [dρ, ρ] using
      RicciFlower.LeviCivita.lcTrace_logDensity (I := I) g hLC x p
  change
    (∑ p : CoordinateIdx (𝕜 := Real) E, C p * dρ p) / ρ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        C p *
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
  rw [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show C p * dρ p * ρ⁻¹ = C p * (dρ p / ρ) by
    rw [div_eq_mul_inv]
    ring]
  rw [htrace p]

/-- Raw divergence bridge after the two contracted component identities have
been supplied: the Voss-Weyl coordinate divergence of `tr_g A` equals the
inverse-metric contraction of `nabla_p A^p_ij`.

The remaining producers for formula 5.10 are now precisely the two contracted
identities `hUtrace` and `hAtrace`: the first is `nabla g^{-1}=0` contracted
with `A`, and the second is the contracted coordinate formula for the
covariant derivative of the `(1,2)` tensor `A`. -/
theorem connTraceRaw_eq_gamma
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hderiv :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (fun y : E =>
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j y *
                  (A ((extChartAt I x).symm y)
                    (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                      (I := I) (M := M) 1 x
                      ((continuousMultilinearMap_basis
                        (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                        (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                    (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x (if q = 0 then i else j)
                        ((extChartAt I x).symm y)))
          (extChartAt I x x)) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              (gInvDeriv p i j *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => p)
                    (fun q : Fin 2 => if q = 0 then i else j) +
                inverseMetricFlatModelInChart_component (I := I) g x i j
                    (extChartAt I x x) *
                  componentDeriv p p i j))
    (hUtrace : ∀ d : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv d i j *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j)) =
        -∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then a else j)) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then i else a))))
    (hAtrace : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ d : CoordinateIdx (𝕜 := Real) E,
        nablaChristoffelVariation x d d i j) =
        (∑ d : CoordinateIdx (𝕜 := Real) E, componentDeriv d d i j) +
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j) *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a a)) -
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a))))) :
    connTraceRawDiv (I := I) g A x =
      gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x := by
  classical
  let U : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j
        (extChartAt I x x)
  let Acomp :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun p i j =>
    componentRS (I := I)
      (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
      (A x) (fun _ : Fin 1 => p) (fun q : Fin 2 => if q = 0 then i else j)
  let Gamma :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun d a k =>
    christoffelSymbolInFrame cov
      (coordinateFrameAt (I := I) x)
      (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k
  have hraw := rawDivTraceAlg
    (U := U) (dU := gInvDeriv) (A := Acomp)
    (dA := componentDeriv)
    (nablaA := fun d k i j => nablaChristoffelVariation x d k i j)
    (Gamma := Gamma)
    (by simpa [U, Acomp, Gamma] using hUtrace)
    (by simpa [U, Acomp, Gamma] using hAtrace)
  rw [connTraceRawDiv_chart_explicit (I := I) g A x]
  rw [hderiv]
  rw [connTraceDensityCorr (I := I) (cov := cov) g hLC A x]
  simpa [gammaRawDivergenceTrace, U, Acomp, Gamma] using hraw

/-- The contracted `nabla g^{-1}=0` input needed by
`connTraceRaw_eq_gamma`.  This is the inverse-metric cancellation specialized
to the point-centered coordinate frame and the upper component slice `A^d_ij`
of the connection-variation tensor. -/
theorem connTraceUTrace
    [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hginvDeriv :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        gInvDeriv d i j =
          extDerivFun (I := I)
            (fun y : M =>
              inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x y))
            x (coordinateFrameAt (I := I) x d x))
    (hzero :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
          (I := I)
          (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
            inverseMetricFlatModelInChart_component (I := I) g x a b
              (extChartAt I x y))
          cov (coordinateFrameAt (I := I) x)
          (coordinateFrameAt_isLocalFrame_one (I := I) x)
          x d i j = 0) :
    ∀ d : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv d i j *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j)) =
        -∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then a else j)) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then i else a))) := by
  classical
  intro d
  let Acomp : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      componentRS (I := I)
        (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
        (A x) (fun _ : Fin 1 => d) (fun q : Fin 2 => if q = 0 then i else j)
  have hcancel :=
    RicciFlower.LeviCivita.gInvTraceCancel
      (I := I)
      (gInv := fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x a b
          (extChartAt I x y))
      (metricDot := fun _ : M => Acomp)
      (cov := cov)
      (frame := coordinateFrameAt (I := I) x)
      (hframe := coordinateFrameAt_isLocalFrame_one (I := I) x)
      (x := x) (d := d) (hzero d)
  calc
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        gInvDeriv d i j *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => d)
            (fun q : Fin 2 => if q = 0 then i else j))
        =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I)
              (fun y : M =>
                inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x y))
              x (coordinateFrameAt (I := I) x d x) *
            Acomp i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hginvDeriv d i j]
    _ =
      -∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                Acomp a j) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                Acomp i a)) := by
        simpa [Acomp] using hcancel
    _ =
      -∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a))) := rfl

/-- Contracted coordinate formula for `nabla_p A^p_ij`, packaged in the exact
shape consumed by `connTraceRaw_eq_gamma`. -/
theorem connTraceATrace
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hNabla : ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ d : CoordinateIdx (𝕜 := Real) E,
        nablaChristoffelVariation x d d i j) =
        (∑ d : CoordinateIdx (𝕜 := Real) E, componentDeriv d d i j) +
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j) *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a a)) -
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a)))) := by
  classical
  intro i j
  let Acomp :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun p i j =>
    componentRS (I := I)
      (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
      (A x) (fun _ : Fin 1 => p) (fun q : Fin 2 => if q = 0 then i else j)
  let Gamma :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun d a k =>
    christoffelSymbolInFrame cov
      (coordinateFrameAt (I := I) x)
      (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k
  have h :=
    traceNablaAlg (A := Acomp) (dA := componentDeriv)
      (nablaA := fun d k i j => nablaChristoffelVariation x d k i j)
      (Gamma := Gamma)
      (by simpa [Acomp, Gamma] using hNabla)
      (by simpa [Gamma] using hGamma)
      i j
  simpa [Acomp, Gamma] using h

/-- Raw-divergence normalization from the three local component producers:
the fixed-chart product rule, the contracted `nabla g^{-1}=0` cancellation,
and the coordinate formula for `nabla A`. -/
theorem connTraceRaw_of_components
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgInvDiff : ∀ x : M, ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x))
    (hADiff : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x))
    (hgInvDeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x) = gInvDeriv x p i j)
    (hADeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x) = componentDeriv x p p i j)
    (hginvExt : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      gInvDeriv x d i j =
        extDerivFun (I := I)
          (fun y : M =>
            inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x y))
          x (coordinateFrameAt (I := I) x d x))
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x a b
            (extChartAt I x y))
        cov (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv x d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    ∀ x : M,
      connTraceRawDiv (I := I) g A x =
        gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x := by
  intro x
  exact connTraceRaw_eq_gamma (I := I) (cov := cov) g hLC A
    nablaChristoffelVariation (gInvDeriv x) (componentDeriv x) x
    (connTraceDeriv (I := I) g A (gInvDeriv x) (componentDeriv x) x
      (hgInvDiff x) (hADiff x) (hgInvDeriv x) (hADeriv x))
    (connTraceUTrace (I := I) (cov := cov) g A (gInvDeriv x) x
      (hginvExt x) (hzero x))
    (connTraceATrace (I := I) (cov := cov) A nablaChristoffelVariation
      (componentDeriv x) x (hNabla x) (hGamma x))

/-- Formula 5.10 using the intrinsic metric trace field `tr_g A` of a smooth
connection-variation tensor.  This specializes `formula510_of_connTrace` with
the smooth section constructed in `Tensor.RSTensor.MetricTrace`. -/
theorem formula510_of_connTraceField
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) (RicciFlower.Realized.connTraceField (I := I) g A) potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :=
  formula510_of_connTrace (I := I) g hpotential hq
    (RicciFlower.Realized.connTraceField (I := I) g A)
    hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hdivTrace hactionTrace hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 assembly with the raw divergence and action trace supplied by
the constructed field `tr_g A` itself.  The remaining geometric bridge is the
single pointwise identity saying the weighted-divergence component produced by
the `δ(Ric + Hess f)` calculation is `div(tr_g A) - (tr_g A)(f)`. -/
theorem formula510_of_trace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  exact formula510_of_connTraceField (I := I) g A hpotential hq hmeas
    hfirst hfinal_int hdiv_int hshift_int hcorr_int
    (rawTrace := connTraceRawDiv (I := I) g A)
    (actionTrace := connTraceAction (I := I) g A potential)
    (fun x => rfl)
    (connTraceAction_eq (I := I) g A potential)
    hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 with the weighted-divergence trace supplied by the coordinate
components of a global connection-variation tensor `A`.

This is the formula-5.10-facing assembly point after the raw divergence bridge:
the fixed-chart product rule, `nabla g^{-1}=0`, and the coordinate formula for
`nabla A` are consumed here to provide the weighted-divergence cancellation. -/
theorem formula510_of_components
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess
            (christoffelWeightedDivergenceTrace (I := I) g
              nablaChristoffelVariation christoffelVariation gradPotential)
            shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable
        (christoffelWeightedDivergenceTrace (I := I) g
          nablaChristoffelVariation christoffelVariation gradPotential)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p)
    (hgInvDiff : ∀ x : M, ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x))
    (hADiff : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x))
    (hgInvDeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x) = gInvDeriv x p i j)
    (hADeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x) = componentDeriv x p p i j)
    (hginvExt : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      gInvDeriv x d i j =
        extDerivFun (I := I)
          (fun y : M =>
            inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x y))
          x (coordinateFrameAt (I := I) x d x))
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x a b
            (extChartAt I x y))
        cov (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv x d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hraw :
      ∀ x : M,
        connTraceRawDiv (I := I) g A x =
          gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x :=
    connTraceRaw_of_components (I := I) (cov := cov) g hLC A
      nablaChristoffelVariation gInvDeriv componentDeriv
      hgInvDiff hADiff hgInvDeriv hADeriv hginvExt hzero hNabla hGamma
  have hweighted :
      ∀ x : M,
        christoffelWeightedDivergenceTrace (I := I) g
            nablaChristoffelVariation christoffelVariation gradPotential x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x :=
    weightedTrace_of_raw (I := I) g A potential nablaChristoffelVariation
      christoffelVariation gradPotential hraw hA hgrad
  exact formula510_of_trace (I := I) g A
    (weightedDivergenceTrace :=
      christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential)
    hpotential hq hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 endpoint producer.

This is the book-facing assembly theorem for the current component route: the
input first variation is the moving-volume derivative of the original
`R + |grad f|^2` bracket, and the theorem uses the per-time weighted IBP
comparison with the closed `R + Delta f` bracket plus the connection-trace
component geometry to produce `FFunctionalFormula510`. -/
theorem formula510_producer
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {s0 : Real}
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov (G.metric s0))
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      shiftedTrace q scalarCurvatureVariation lapPotentialVariation
      gradPotentialNormSqVariation : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hfirstVariation :
      firstVariation =
        ∫ x,
          expWeightedIntegralVariationIntegrand
            (potentialPath s0) potentialVariation metricVariationTrace
            (fFunctionalBracket (scalarCurvaturePath s0)
              (gradPotentialNormSqPath s0))
            (fFunctionalBracketVariation scalarCurvatureVariation
              gradPotentialNormSqVariation) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s0))
    (hmeas_near :
      ∀ᶠ s in nhds s0,
        AEMeasurable
          (fun x : M =>
            ENNReal.ofReal (expNegPotentialDensity (potentialPath s) x))
          (volumeMeasureFamily (I := I) (M := M) G s))
    (hibp_near :
      ∀ᶠ s in nhds s0,
        (∫ x,
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s))) =
        ∫ x,
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s)))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential)
    (hclosed_variation :
      ∀ x : M,
        fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation x =
          -metricVariationRicciHess x +
            christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
              nablaChristoffelVariation christoffelVariation gradPotential x +
            shiftedTrace x)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hdiv_int :
      Integrable
        (christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
          nablaChristoffelVariation christoffelVariation gradPotential)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p)
    (hgInvDiff : ∀ x : M, ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x i j y)
        (extChartAt I x x))
    (hADiff : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x))
    (hgInvDeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x i j y)
        (extChartAt I x x) = gInvDeriv x p i j)
    (hADeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x) = componentDeriv x p p i j)
    (hginvExt : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      gInvDeriv x d i j =
        extDerivFun (I := I)
          (fun y : M =>
            inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x i j
              (extChartAt I x y))
          x (coordinateFrameAt (I := I) x d x))
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x a b
            (extChartAt I x y))
        cov (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv x d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) (G.metric s0) hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          (G.metric s0).inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) (G.metric s0) hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) (G.metric s0) hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) (G.metric s0) hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hfirst_pre :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess
            (christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
              nablaChristoffelVariation christoffelVariation gradPotential)
            shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
              potential) := by
    refine hfirstVariation.trans ?_
    exact firstVar_pre510_ibp (I := I) (M := M) G hmeas hmeas_near
      hibp_near hscalar_deriv hgrad_deriv hlap_deriv hpotential_deriv
      htrace hmetric_reg horig_reg hclosed_reg hpotential0 hscalar0 hlap0
      hclosed_variation
  exact formula510_of_components (I := I) (cov := cov) (G.metric s0) hLC A
    nablaChristoffelVariation christoffelVariation gradPotential
    gInvDeriv componentDeriv hpotential hq hmeas hfirst_pre
    hfinal_int hdiv_int hshift_int hcorr_int hA hgrad
    hgInvDiff hADiff hgInvDeriv hADeriv hginvExt hzero hNabla hGamma
    hlap hgradSq hshift hqeq

end GeometryFormula510

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
