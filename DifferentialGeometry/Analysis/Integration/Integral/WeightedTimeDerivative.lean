import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz


noncomputable section

open Filter MeasureTheory Set
open scoped Interval

namespace LocallyLipschitzOn

variable {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {a b : ℝ}

theorem absolutelyContinuousOnInterval
    (hf : LocallyLipschitzOn (uIcc a b) f) : AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith_of_compact isCompact_uIcc
  exact hK.absolutelyContinuousOnInterval

end LocallyLipschitzOn

namespace AbsolutelyContinuousOnInterval

variable {f rho phi v c : ℝ → ℝ} {a b : ℝ}

theorem integral_weighted_deriv_mul
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hrho : AbsolutelyContinuousOnInterval rho a b)
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hv : v =ᵐ[volume.restrict (uIoc a b)] deriv f)
    (hrhoDeriv : deriv rho =ᵐ[volume.restrict (uIoc a b)] fun t => c t * rho t) :
    (∫ t in a..b, rho t * (v t + c t * f t) * phi t) =
      rho b * f b * phi b - rho a * f a * phi a -
        ∫ t in a..b, rho t * f t * deriv phi t := by
  have hbase := (hrho.fun_mul hf).integral_mul_deriv_eq_deriv_mul hphi
  have hderiv : (∫ t in a..b, deriv (fun s => rho s * f s) t * phi t) =
      ∫ t in a..b, rho t * (v t + c t * f t) * phi t := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hv, hrhoDeriv, ae_restrict_of_ae hf.ae_differentiableAt,
      ae_restrict_of_ae hrho.ae_differentiableAt,
      ae_restrict_mem measurableSet_uIoc] with t hvt hrt hft hrhot ht
    have hmul := (hrhot (uIoc_subset_uIcc ht)).hasDerivAt.mul
      (hft (uIoc_subset_uIcc ht)).hasDerivAt
    change HasDerivAt (fun s => rho s * f s) _ t at hmul
    rw [hmul.deriv, hrt, ← hvt]
    ring
  rw [hderiv] at hbase
  linarith only [hbase]

theorem integral_weighted_deriv_mul_eq_neg
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hrho : AbsolutelyContinuousOnInterval rho a b)
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hv : v =ᵐ[volume.restrict (uIoc a b)] deriv f)
    (hrhoDeriv : deriv rho =ᵐ[volume.restrict (uIoc a b)] fun t => c t * rho t)
    (hleft : phi a = 0) (hright : phi b = 0) :
    (∫ t in a..b, rho t * (v t + c t * f t) * phi t) =
      -(∫ t in a..b, rho t * f t * deriv phi t) := by
  simpa only [hleft, hright, mul_zero, sub_zero, zero_sub] using
    hf.integral_weighted_deriv_mul hrho hphi hv hrhoDeriv

end AbsolutelyContinuousOnInterval

namespace DifferentialGeometry.Analysis

variable {X : Type*} [MeasurableSpace X] {mu : Measure X} [SFinite mu]
  {u rho phi v c : ℝ → X → ℝ} {a b : ℝ}

theorem integral_integral_weighted_time_deriv
    (hu : ∀ᵐ x ∂mu, AbsolutelyContinuousOnInterval (fun t => u t x) a b)
    (hrho : ∀ᵐ x ∂mu, AbsolutelyContinuousOnInterval (fun t => rho t x) a b)
    (hphi : ∀ᵐ x ∂mu, AbsolutelyContinuousOnInterval (fun t => phi t x) a b)
    (hv : ∀ᵐ x ∂mu, (fun t => v t x) =ᵐ[volume.restrict (uIoc a b)]
      deriv (fun t => u t x))
    (hrhoDeriv : ∀ᵐ x ∂mu, deriv (fun t => rho t x) =ᵐ[volume.restrict (uIoc a b)]
      fun t => c t x * rho t x)
    (hboundary : ∀ᵐ x ∂mu, phi a x = 0 ∧ phi b x = 0)
    (hleft : Integrable (fun p : ℝ × X =>
      rho p.1 p.2 * (v p.1 p.2 + c p.1 p.2 * u p.1 p.2) * phi p.1 p.2)
      ((volume.restrict (uIoc a b)).prod mu))
    (hright : Integrable (fun p : ℝ × X =>
      rho p.1 p.2 * u p.1 p.2 * deriv (fun t => phi t p.2) p.1)
      ((volume.restrict (uIoc a b)).prod mu)) :
    (∫ t in a..b, ∫ x, rho t x * (v t x + c t x * u t x) * phi t x ∂mu) =
      -(∫ t in a..b, ∫ x, rho t x * u t x * deriv (fun s => phi s x) t ∂mu) := by
  rw [intervalIntegral_integral_swap hleft, intervalIntegral_integral_swap hright,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hu, hrho, hphi, hv, hrhoDeriv, hboundary]
    with x hux hrhox hphix hvx hrhoDerivx hboundaryx
  exact hux.integral_weighted_deriv_mul_eq_neg hrhox hphix hvx hrhoDerivx
    hboundaryx.1 hboundaryx.2

theorem integral_integral_weighted_time_deriv_of_locallyLipschitzOn
    (hu : ∀ᵐ x ∂mu, LocallyLipschitzOn (uIcc a b) (fun t => u t x))
    (hrho : ∀ᵐ x ∂mu, AbsolutelyContinuousOnInterval (fun t => rho t x) a b)
    (hphi : ∀ᵐ x ∂mu, AbsolutelyContinuousOnInterval (fun t => phi t x) a b)
    (hrhoDeriv : ∀ᵐ x ∂mu, deriv (fun t => rho t x) =ᵐ[volume.restrict (uIoc a b)]
      fun t => c t x * rho t x)
    (hboundary : ∀ᵐ x ∂mu, phi a x = 0 ∧ phi b x = 0)
    (hleft : Integrable (fun p : ℝ × X => rho p.1 p.2 *
      (deriv (fun t => u t p.2) p.1 + c p.1 p.2 * u p.1 p.2) * phi p.1 p.2)
      ((volume.restrict (uIoc a b)).prod mu))
    (hright : Integrable (fun p : ℝ × X =>
      rho p.1 p.2 * u p.1 p.2 * deriv (fun t => phi t p.2) p.1)
      ((volume.restrict (uIoc a b)).prod mu)) :
    (∫ t in a..b, ∫ x, rho t x *
      (deriv (fun s => u s x) t + c t x * u t x) * phi t x ∂mu) =
      -(∫ t in a..b, ∫ x, rho t x * u t x * deriv (fun s => phi s x) t ∂mu) :=
  integral_integral_weighted_time_deriv
    (hu.mono fun _ hx => hx.absolutelyContinuousOnInterval) hrho hphi
    (Eventually.of_forall fun _ => Filter.EventuallyEq.rfl) hrhoDeriv hboundary hleft hright

end DifferentialGeometry.Analysis
