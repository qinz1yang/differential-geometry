/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Perelman.Entropy
import RicciFlower.Analysis.VolumeVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Elementary variation producers for Perelman's `W`

This file contains the first actual derivative producers for MSM135 Lemma 6.1.
The geometric first variation of Perelman's `F` functional is intentionally not
proved here; the scalar-curvature and gradient-square derivatives remain scalar
inputs.
-/

namespace RicciFlower
namespace RicciFlow
namespace Perelman

noncomputable section

open Filter MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open scoped Manifold ContDiff

variable {M : Type*}

/-! ## Scalar pointwise producers -/

theorem perelmanDensityPrefactor_hasDerivAt {n : Nat}
    {tauPath : Real -> Real} {s0 tau tauVariation : Real}
    (htau : tauPath s0 = tau) (htau_pos : 0 < tau)
    (htau_deriv : HasDerivAt tauPath tauVariation s0) :
    HasDerivAt
      (fun s : Real => perelmanDensityPrefactor n (tauPath s))
      (-((n : Real) / (2 * tau)) * tauVariation *
        perelmanDensityPrefactor n tau)
      s0 := by
  have hbase :
      HasDerivAt (fun s : Real => 4 * Real.pi * tauPath s)
        ((4 * Real.pi) * tauVariation) s0 := by
    simpa [mul_assoc] using htau_deriv.const_mul (4 * Real.pi)
  have hbase_ne :
      4 * Real.pi * tauPath s0 ≠ 0 := by
    rw [htau]
    positivity
  have hderiv :
      HasDerivAt
        (fun s : Real => (4 * Real.pi * tauPath s) ^ (-(n : Real) / 2))
        (((4 * Real.pi) * tauVariation) * (-(n : Real) / 2) *
          (4 * Real.pi * tauPath s0) ^ (-(n : Real) / 2 - 1))
        s0 :=
    hbase.rpow_const (Or.inl hbase_ne)
  convert hderiv using 1
  unfold perelmanDensityPrefactor
  rw [htau]
  have hbase_tau_ne : 4 * Real.pi * tau ≠ 0 := by positivity
  rw [Real.rpow_sub_one hbase_tau_ne]
  field_simp [htau_pos.ne', hbase_tau_ne]
  ring_nf
  rfl

/-- Pointwise derivative of Perelman's density
`u = (4*pi*tau)^(-n/2) * exp (-f)`. -/
theorem perelmanDensity_hasDerivAt {n : Nat}
    {tauPath : Real -> Real} {potentialPath : Real -> M -> Real}
    {s0 tau tauVariation : Real}
    {potentialVariation : M -> Real}
    (htau : tauPath s0 = tau) (htau_pos : 0 < tau)
    (htau_deriv : HasDerivAt tauPath tauVariation s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real => perelmanDensity n (tauPath s) (potentialPath s) x)
      ((-((n : Real) / (2 * tau)) * tauVariation -
          potentialVariation x) *
        perelmanDensity n tau (potentialPath s0) x)
      s0 := by
  have hpref :=
    perelmanDensityPrefactor_hasDerivAt
      (n := n) (tauPath := tauPath) (s0 := s0) (tau := tau)
      (tauVariation := tauVariation) htau htau_pos htau_deriv
  have hexp :
      HasDerivAt
        (fun s : Real => Real.exp (-(potentialPath s x)))
        (Real.exp (-(potentialPath s0 x)) * (-(potentialVariation x)))
        s0 := by
    simpa using (hpotential_deriv x).neg.exp
  have hmul := hpref.mul hexp
  convert hmul using 1
  unfold perelmanDensity
  rw [htau]
  ring_nf

/-- Scalar derivative of the bracket
`tau * (R + |grad f|^2) + f - n`. -/
def wEntropyBracketVariation (tau tauVariation : Real)
    (scalarCurvature scalarCurvatureVariation gradPotentialNormSq
      gradPotentialNormSqVariation potentialVariation : M -> Real) :
    M -> Real :=
  fun x =>
    tauVariation * (scalarCurvature x + gradPotentialNormSq x) +
      tau * (scalarCurvatureVariation x + gradPotentialNormSqVariation x) +
        potentialVariation x

theorem wEntropyBracket_hasDerivAt {n : Nat}
    {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 tau tauVariation : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation :
      M -> Real}
    (htau : tauPath s0 = tau)
    (htau_deriv : HasDerivAt tauPath tauVariation s0)
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
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s) x)
      (wEntropyBracketVariation tau tauVariation (scalarCurvaturePath s0)
        scalarCurvatureVariation (gradPotentialNormSqPath s0)
        gradPotentialNormSqVariation potentialVariation x)
      s0 := by
  have hsum := (hscalar_deriv x).add (hgrad_deriv x)
  have hprod := htau_deriv.mul hsum
  have hmain := (hprod.add (hpotential_deriv x)).sub_const (n : Real)
  convert hmain using 1
  unfold wEntropyBracketVariation
  rw [htau]
  simp only [Pi.add_apply]

/-! ## Base-integral producers -/

/-- The scalar integrand produced by differentiating
`phi_s * u_s dmu_s`, where `u_s` is Perelman's density and `dmu_s` is the
Riemannian volume measure. -/
def wEntropyWeightedIntegralVariationIntegrand (n : Nat)
    (tau tauVariation : Real)
    (potential potentialVariation metricVariationTrace phi phiVariation :
      M -> Real) :
    M -> Real :=
  fun x =>
    perelmanDensity n tau potential x *
      (phiVariation x +
        phi x *
          wEntropyWeightedMeasureVariationFactor n tau tauVariation
            potentialVariation metricVariationTrace x)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Moving-volume derivative for integrals against Perelman's weighted density.

The regularity hypothesis is exactly the one required by
`volume_variation_formula_clean_at` for the base-measure integrand
`u_s * phi_s`; deriving it from spacetime smoothness is a later analytic
regularity bridge. -/
theorem weightedMeasureIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {n : Nat} {tauPath : Real -> Real}
    {potentialPath : Real -> M -> Real}
    {phiPath : Real -> M -> Real}
    {s0 tau tauVariation : Real}
    {potentialVariation metricVariationTrace phiVariation : M -> Real}
    (htau : tauPath s0 = tau) (htau_pos : 0 < tau)
    (htau_deriv : HasDerivAt tauPath tauVariation s0)
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
          perelmanDensity n (tauPath s) (potentialPath s) x * phiPath s x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          perelmanDensity n (tauPath s) (potentialPath s) x * phiPath s x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        wEntropyWeightedIntegralVariationIntegrand n tau tauVariation
          (potentialPath s0) potentialVariation metricVariationTrace
          (phiPath s0) phiVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  have hvol :=
    volume_variation_formula_clean_at
      (I := I) (M := M) G
      (f := fun s : Real => fun x : M =>
        perelmanDensity n (tauPath s) (potentialPath s) x * phiPath s x)
      (t₀ := s0) hmetric_reg hintegrand_reg
  refine hvol.congr_deriv ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hdens :=
    perelmanDensity_hasDerivAt
      (M := M) (n := n) (tauPath := tauPath)
      (potentialPath := potentialPath) (s0 := s0) (tau := tau)
      (tauVariation := tauVariation) htau htau_pos htau_deriv
      hpotential_deriv x
  have hprod :
      HasDerivAt
        (fun s : Real =>
          perelmanDensity n (tauPath s) (potentialPath s) x * phiPath s x)
        (((-((n : Real) / (2 * tau)) * tauVariation -
            potentialVariation x) *
          perelmanDensity n tau (potentialPath s0) x) * phiPath s0 x +
          perelmanDensity n (tauPath s0) (potentialPath s0) x *
            phiVariation x)
        s0 :=
    hdens.mul (hphi_deriv x)
  have hderiv := hprod.deriv
  change
    deriv
        (fun s : Real =>
          perelmanDensity n (tauPath s) (potentialPath s) x * phiPath s x)
        s0 +
      1 / 2 * traceTimeDerivMetricAt (I := I) G s0 x *
        (perelmanDensity n (tauPath s0) (potentialPath s0) x * phiPath s0 x) =
    wEntropyWeightedIntegralVariationIntegrand n tau tauVariation
      (potentialPath s0) potentialVariation metricVariationTrace
      (phiPath s0) phiVariation x
  rw [hderiv, htrace x, htau]
  unfold wEntropyWeightedIntegralVariationIntegrand
    wEntropyWeightedMeasureVariationFactor
  ring

/-- Formula specialized to the `W` bracket.  The scalar derivatives of
curvature and `|grad f|^2` are inputs; formula 5.10 is the later geometric
producer that identifies them. -/
theorem wEntropyBaseIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {n : Nat} {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 tau tauVariation : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (htau : tauPath s0 = tau) (htau_pos : 0 < tau)
    (htau_deriv : HasDerivAt tauPath tauVariation s0)
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
          perelmanDensity n (tauPath s) (potentialPath s) x *
            wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) (potentialPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          perelmanDensity n (tauPath s) (potentialPath s) x *
            wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) (potentialPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        wEntropyWeightedIntegralVariationIntegrand n tau tauVariation
          (potentialPath s0) potentialVariation metricVariationTrace
          (wEntropyBracket n tau (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0) (potentialPath s0))
          (wEntropyBracketVariation tau tauVariation (scalarCurvaturePath s0)
            scalarCurvatureVariation (gradPotentialNormSqPath s0)
            gradPotentialNormSqVariation potentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  simpa [htau] using
    (weightedMeasureIntegral_hasDerivAt_at
      (I := I) (M := M) G
      (n := n) (tauPath := tauPath) (potentialPath := potentialPath)
      (phiPath := fun s : Real => fun x : M =>
        wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s) x)
      (s0 := s0) (tau := tau) (tauVariation := tauVariation)
      (potentialVariation := potentialVariation)
      (metricVariationTrace := metricVariationTrace)
      (phiVariation :=
        wEntropyBracketVariation tau tauVariation (scalarCurvaturePath s0)
          scalarCurvatureVariation (gradPotentialNormSqPath s0)
          gradPotentialNormSqVariation potentialVariation)
      htau htau_pos htau_deriv hpotential_deriv
      (wEntropyBracket_hasDerivAt
        (M := M) (n := n) (tauPath := tauPath)
        (scalarCurvaturePath := scalarCurvaturePath)
        (gradPotentialNormSqPath := gradPotentialNormSqPath)
        (potentialPath := potentialPath) (s0 := s0) (tau := tau)
        (tauVariation := tauVariation)
        (scalarCurvatureVariation := scalarCurvatureVariation)
        (gradPotentialNormSqVariation := gradPotentialNormSqVariation)
        (potentialVariation := potentialVariation)
        htau htau_deriv hscalar_deriv hgrad_deriv hpotential_deriv)
      htrace hmetric_reg hintegrand_reg)

/-- Convert a base-integral derivative into the path-level first-variation
predicate for `W`.  The eventual equality isolates the routine but verbose
`withDensity` measurability conversion. -/
theorem WEntropyHasFirstVariationAt_of_baseIntegral_hasDerivAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M} {n : Nat} {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 firstVariation : Real}
    (hbase_eq :
      (fun s : Real =>
        wFunctional (muPath s) n (tauPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          perelmanDensity n (tauPath s) (potentialPath s) x *
            wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) (potentialPath s) x
          ∂(muPath s))
    (hbase :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            perelmanDensity n (tauPath s) (potentialPath s) x *
              wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) (potentialPath s) x
            ∂(muPath s))
        firstVariation s0) :
    WEntropyHasFirstVariationAt muPath n tauPath scalarCurvaturePath
      gradPotentialNormSqPath potentialPath s0 firstVariation := by
  unfold WEntropyHasFirstVariationAt wFunctionalAlong
  exact hbase.congr_of_eventuallyEq hbase_eq

/-- `WEntropyHasFirstVariationAt` producer obtained from the moving-volume
formula, plus the local equality between `W` and the corresponding base
integral. -/
theorem WEntropyHasFirstVariationAt_of_volumeVariation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {n : Nat} {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 tau tauVariation : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hbase_eq :
      (fun s : Real =>
        wFunctional (volumeMeasureFamily (I := I) (M := M) G s) n
          (tauPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          perelmanDensity n (tauPath s) (potentialPath s) x *
            wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) (potentialPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (htau : tauPath s0 = tau) (htau_pos : 0 < tau)
    (htau_deriv : HasDerivAt tauPath tauVariation s0)
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
          perelmanDensity n (tauPath s) (potentialPath s) x *
            wEntropyBracket n (tauPath s) (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) (potentialPath s) x)
        s0) :
    WEntropyHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G)
      n tauPath scalarCurvaturePath gradPotentialNormSqPath potentialPath s0
      (∫ x,
        wEntropyWeightedIntegralVariationIntegrand n tau tauVariation
          (potentialPath s0) potentialVariation metricVariationTrace
          (wEntropyBracket n tau (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0) (potentialPath s0))
          (wEntropyBracketVariation tau tauVariation (scalarCurvaturePath s0)
            scalarCurvatureVariation (gradPotentialNormSqPath s0)
            gradPotentialNormSqVariation potentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) := by
  exact WEntropyHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    hbase_eq
    (wEntropyBaseIntegral_hasDerivAt_at
      (I := I) (M := M) G
      htau htau_pos htau_deriv hscalar_deriv hgrad_deriv
      hpotential_deriv htrace hmetric_reg hintegrand_reg)

end Geometry

end

end Perelman
end RicciFlow
end RicciFlower
