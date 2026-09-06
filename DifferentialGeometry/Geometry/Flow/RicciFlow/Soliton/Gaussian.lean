import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.ODE
  (curveAt_integralCurve integralCurve_eq_of_agree_zero)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]

theorem canonicalFlowMap_gaussian (s : Real) (x : E) :
    canonicalFlowMap (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian s x =
      Real.exp (s / 2) • x := by
  have hcurve : IsMIntegralCurve (fun r : Real => Real.exp (r / 2) • x)
      (fun y => gradFun (euclideanMetric (E := E)) gaussianPotential y) := by
    intro r
    have hderiv : HasDerivAt (fun u : Real => Real.exp (u / 2) • x)
        ((1 / 2 : Real) • (Real.exp (r / 2) • x)) r := by
      simpa only [id_eq, smul_smul, mul_comm] using
        (((hasDerivAt_id r).div_const 2).exp).smul_const x
    rw [← gaussianPotential_gradFun] at hderiv
    exact hderiv.hasFDerivAt.hasMFDerivAt
  have hcanonical : IsMIntegralCurve
      (fun r : Real => canonicalFlowMap (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian r x)
      (fun y => gradFun (euclideanMetric (E := E)) gaussianPotential y) := by
    unfold canonicalFlowMap
    exact curveAt_integralCurve _ _ x
  have hregular :=
    (DifferentialGeometry.Geometry.Connection.gradFun_contMDiff_total_section
      (euclideanMetric (E := E))
      (gaussianPotential (E := E)).contMDiff).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hinitial : canonicalFlowMap (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian 0 x =
      Real.exp ((0 : Real) / 2) • x := by
    simpa using congrFun (canonicalFlowMap_zero (euclideanMetric (E := E))
      gaussianPotential 1 euclideanMetric_complete gradientRicciSoliton_gaussian) x
  exact congrFun (integralCurve_eq_of_agree_zero _ hregular hcanonical hcurve hinitial) s

theorem canonicalFlowDiffeomorph_gaussian
    {t : Real} (ht : t ∈ canonicalTimeDomain 1) (x : E) :
    canonicalFlowDiffeomorph (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian
        (canonicalFlowParameter 1 t) x =
      (1 - t) ^ (-(1 / 2 : Real)) • x := by
  rw [canonicalFlowDiffeomorph_apply, canonicalFlowMap_gaussian]
  have hpos : 0 < 1 - t := by
    simpa only [one_mul] using mem_canonicalTimeDomain_iff.mp ht
  have hparameter : canonicalFlowParameter 1 t = -Real.log (1 - t) := by
    simp only [canonicalFlowParameter, one_ne_zero, if_false, one_mul, div_one]
  rw [hparameter, Real.rpow_def_of_pos hpos]
  congr 2
  ring

theorem canonicalMetric_gaussian
    {t : Real} (ht : t ∈ canonicalTimeDomain 1) :
    canonicalMetric (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian ht =
      euclideanMetric (E := E) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hderiv : ∀ s ∈ Set.Iio (1 : Real),
      HasDerivAt
        (fun r : Real =>
          (canonicalMetricFamily (euclideanMetric (E := E)) gaussianPotential 1
            euclideanMetric_complete gradientRicciSoliton_gaussian r).inner x v w)
        0 s := by
    intro s hs
    have hsDomain : s ∈ canonicalTimeDomain 1 := by
      change 0 < 1 - 1 * s
      simpa only [one_mul] using sub_pos.mpr hs
    have hflow := canonicalMetricFamily_ricciFlow
      (euclideanMetric (E := E)) gaussianPotential 1
      euclideanMetric_complete gradientRicciSoliton_gaussian hsDomain x v w
    rw [canonicalMetricFamily_eq _ _ _ _ _ hsDomain,
      canonicalMetric, ricciTensor_pullback, ricciTensor_scaleMetric,
      euclideanMetric_ricciTensor, mul_zero] at hflow
    exact hflow
  have htOne : t < 1 := by
    have hpos := mem_canonicalTimeDomain_iff.mp ht
    linarith
  have heq := isOpen_Iio.is_const_of_deriv_eq_zero
    (convex_Iio (1 : Real)).isPreconnected
    (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hderiv s hs).deriv) htOne (show (0 : Real) < 1 by norm_num)
  rw [canonicalMetricFamily_eq _ _ _ _ _ ht, canonicalMetricFamily_zero] at heq
  exact heq

theorem canonicalMetricFamily_gaussian (t : Real) :
    canonicalMetricFamily (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian t =
      euclideanMetric (E := E) := by
  by_cases ht : t ∈ canonicalTimeDomain 1
  · rw [canonicalMetricFamily_eq _ _ _ _ _ ht]
    exact canonicalMetric_gaussian ht
  · simp only [canonicalMetricFamily, dif_neg ht]

theorem canonicalPotential_gaussian
    {t : Real} (ht : t ∈ canonicalTimeDomain 1) (x : E) :
    canonicalPotential (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian t x =
      ‖x‖ ^ 2 / (4 * (1 - t)) := by
  have hderiv : ∀ s ∈ Set.Iio (1 : Real),
      HasDerivAt
        (fun r : Real => (1 - r) *
          canonicalPotential (euclideanMetric (E := E)) gaussianPotential 1
            euclideanMetric_complete gradientRicciSoliton_gaussian r x)
        0 s := by
    intro s hs
    have hpos : 0 < 1 - s := sub_pos.mpr hs
    have hsDomain : s ∈ canonicalTimeDomain 1 := by
      change 0 < 1 - 1 * s
      simpa only [one_mul] using hpos
    have hevol := canonicalPotential_evolution
      (euclideanMetric (E := E)) gaussianPotential 1
      euclideanMetric_complete gradientRicciSoliton_gaussian hsDomain x
    simp only [one_mul, gaussianPotential_normGradSqFun] at hevol
    have hpotential :
        canonicalPotential (euclideanMetric (E := E)) gaussianPotential 1
          euclideanMetric_complete gradientRicciSoliton_gaussian s x =
        gaussianPotential
          (canonicalFlowMap (euclideanMetric (E := E)) gaussianPotential 1
            euclideanMetric_complete gradientRicciSoliton_gaussian
            (canonicalFlowParameter 1 s) x) := by
      change gaussianPotential
          (canonicalFlowDiffeomorph (euclideanMetric (E := E)) gaussianPotential 1
            euclideanMetric_complete gradientRicciSoliton_gaussian
            (canonicalFlowParameter 1 s) x) = _
      rw [canonicalFlowDiffeomorph_apply]
    rw [← hpotential] at hevol
    have hscale : HasDerivAt (fun r : Real => 1 - r) (-1) s := by
      change HasDerivAt ((fun _ : Real => 1) - id) (-1) s
      simpa only [zero_sub] using
        (hasDerivAt_const s (1 : Real)).sub (hasDerivAt_id s)
    apply (hscale.mul hevol).congr_deriv
    field_simp [ne_of_gt hpos]
    ring
  have hpos : 0 < 1 - t := by
    simpa only [one_mul] using mem_canonicalTimeDomain_iff.mp ht
  have heq := isOpen_Iio.is_const_of_deriv_eq_zero
    (convex_Iio (1 : Real)).isPreconnected
    (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hderiv s hs).deriv)
    (sub_pos.mp hpos) (show (0 : Real) < 1 by norm_num)
  have hvalue : (1 - t) *
      canonicalPotential (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian t x =
      gaussianPotential x := by
    simpa only [sub_zero, one_mul, canonicalPotential_zero] using heq
  calc
    canonicalPotential (euclideanMetric (E := E)) gaussianPotential 1
        euclideanMetric_complete gradientRicciSoliton_gaussian t x =
      gaussianPotential x / (1 - t) :=
        (eq_div_iff (ne_of_gt hpos)).2 (by simpa only [mul_comm] using hvalue)
    _ = ‖x‖ ^ 2 / (4 * (1 - t)) := by
      rw [gaussianPotential_apply, div_div]

end DifferentialGeometry.PDE.RicciFlow.Soliton
