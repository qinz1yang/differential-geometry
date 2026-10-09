import DifferentialGeometry.Geometry.Metric.CurveEnergy.IntegralComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalBlowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Analysis.Integration.Integral.LogarithmicLowerBound

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem standard_unweighted_action_ge_log :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : StandardSolution) (gamma : ℝ → E3),
      ∀ theta ∈ Ico (0 : ℝ) 1,
        ENNReal.ofReal (c * Real.log ((1 - theta)⁻¹)) ≤
          ∫⁻ t in Ioc (0 : ℝ) theta, ENNReal.ofReal
            (metricScalarAt (S.val.metric t) (gamma t) +
              (S.val.metric t).inner (gamma t) (lVelocity gamma t) (lVelocity gamma t)) := by
  obtain ⟨c, hc, hscalar⟩ := exists_standard_scalar_lower_bound
  refine ⟨c, hc, ?_⟩
  intro S gamma theta htheta
  rw [show (1 - theta)⁻¹ = ((1 : ℝ) - 0) / (1 - theta) by simp]
  apply DifferentialGeometry.Analysis.ofReal_mul_log_le_lintegral_of_reciprocal_lower_bound
    hc.le htheta.1 htheta.2
  intro t ht
  exact (hscalar S (gamma t) t ⟨ht.1.le, ht.2.trans_lt htheta.2⟩).trans
    (le_add_of_nonneg_right (DifferentialGeometry.metric_inner_self_nonneg _ _ _))

theorem exists_standard_full_duration_action_lower_bound (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ ∀ (S : StandardSolution) (gamma : ℝ → E3),
      ENNReal.ofReal Lambda <
        ∫⁻ t in Ioc (0 : ℝ) theta, ENNReal.ofReal
          (metricScalarAt (S.val.metric t) (gamma t) +
            (S.val.metric t).inner (gamma t) (lVelocity gamma t) (lVelocity gamma t)) := by
  obtain ⟨c, hc, hbound⟩ := standard_unweighted_action_ge_log
  obtain ⟨theta, htheta, hlarge⟩ :=
    DifferentialGeometry.Analysis.exists_logarithmic_integral_lower_bound hc Lambda
  refine ⟨theta, htheta, fun S gamma => ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLambda.le).mpr hlarge |>.trans_le
    (hbound S gamma theta ⟨htheta.1.le, htheta.2⟩)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_standard_action_lower_bound_of_endpoint_separation
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) 1) (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ r : ℝ, 0 < r ∧ ∀ (S : StandardSolution) (gamma : ℝ → E3) (tau : ℝ),
      0 < tau → tau ≤ theta → ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 tau) →
      ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric (gamma 0) (gamma tau) →
      ENNReal.ofReal Lambda <
        ∫⁻ t in Ioc (0 : ℝ) tau, ENNReal.ofReal
          (metricScalarAt (S.val.metric t) (gamma t) +
            (S.val.metric t).inner (gamma t) (lVelocity gamma t) (lVelocity gamma t)) := by
  obtain ⟨hlife, K, hK, hcurv⟩ := uniformStandardLifetime_slab theta htheta.1.le
    (by rw [uniformStandardLifetime_eq_one]; exact ENNReal.ofReal_lt_one.mpr htheta.2)
  obtain ⟨C, hC, _, _, _, _, hmetric⟩ := standard_metric_bounds_on_shorter_windows theta K htheta.1.le hK
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let r := Real.sqrt (C * (Lambda + 1))
  have hrad : 0 < C * (Lambda + 1) := mul_pos hCpos (by linarith)
  have hr : 0 < r := Real.sqrt_pos.mpr hrad
  refine ⟨r, hr, ?_⟩
  intro S gamma tau htau hle hgamma hsep
  obtain ⟨c, hc, hscalar⟩ := exists_standard_scalar_lower_bound
  have hlow := ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation
    StandardCap.metric htau (inv_nonneg.mpr hCpos.le) hr.le hgamma
    (fun t => metricScalarAt (S.val.metric t) (gamma t) +
      (S.val.metric t).inner (gamma t) (lVelocity gamma t) (lVelocity gamma t)) ?_ hsep
  · rw [sub_zero] at hlow
    have hr2 : r ^ 2 = C * (Lambda + 1) := Real.sq_sqrt hrad.le
    have heq : C⁻¹ * r ^ 2 = Lambda + 1 := by rw [hr2]; field_simp
    rw [heq] at hlow
    have hstrict : Lambda < (Lambda + 1) / tau := by
      apply (lt_div_iff₀ htau).mpr
      have hh := mul_le_mul_of_nonneg_left (hle.trans htheta.2.le) hLambda.le
      nlinarith
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLambda.le).mpr hstrict |>.trans_le hlow
  intro t ht
  have htTheta : t ∈ Icc 0 theta := ⟨ht.1.le, ht.2.trans hle⟩
  have hmet := ((hmetric S.val theta htheta.1.le le_rfl (hlife S) (hcurv S)).1
    t htTheta).2 (gamma t) (mem_univ _) (lVelocity gamma t)
  have hsc := hscalar S (gamma t) t ⟨ht.1.le, htTheta.2.trans_lt htheta.2⟩
  have hnonneg : 0 ≤ metricScalarAt (S.val.metric t) (gamma t) :=
    (div_nonneg hc.le (by linarith [htTheta.2, htheta.2])).trans hsc
  exact hmet.1.trans (le_add_of_nonneg_left hnonneg)

theorem exists_standard_unweighted_action_lower_bound
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧
      ∀ (S : StandardSolution) (gamma : ℝ → E3) (tau : ℝ),
        0 < tau → tau ≤ theta → ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 tau) →
        (tau = theta ∨
          ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric (gamma 0) (gamma tau)) →
        ENNReal.ofReal Lambda <
          ∫⁻ t in Ioc (0 : ℝ) tau, ENNReal.ofReal
            (metricScalarAt (S.val.metric t) (gamma t) +
              (S.val.metric t).inner (gamma t) (lVelocity gamma t) (lVelocity gamma t)) := by
  obtain ⟨theta, htheta, hlong⟩ := exists_standard_full_duration_action_lower_bound Lambda hLambda
  obtain ⟨r, hr, hfar⟩ := exists_standard_action_lower_bound_of_endpoint_separation htheta Lambda hLambda
  refine ⟨theta, r, htheta, hr, ?_⟩
  intro S gamma tau htau hle hgamma halt
  rcases halt with rfl | hfarther
  · exact hlong S gamma
  · exact hfar S gamma tau htau hle hgamma hfarther

theorem exists_standard_unweighted_action_lower_bound_of_ball_exit
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧
      ∀ (S : StandardSolution) (gamma : ℝ → E3) (tau : ℝ),
        0 < tau → tau ≤ theta → ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 tau) →
        riemannianEDistOf StandardCap.metric 0 (gamma 0) ≤ ENNReal.ofReal r →
        (tau = theta ∨
          ENNReal.ofReal (2 * r) ≤ riemannianEDistOf StandardCap.metric 0 (gamma tau)) →
        ENNReal.ofReal Lambda <
          ∫⁻ t in Ioc (0 : ℝ) tau, ENNReal.ofReal
            (metricScalarAt (S.val.metric t) (gamma t) +
              (S.val.metric t).inner (gamma t) (lVelocity gamma t) (lVelocity gamma t)) := by
  obtain ⟨theta, r, htheta, hr, hbound⟩ := exists_standard_unweighted_action_lower_bound Lambda hLambda
  refine ⟨theta, r, htheta, hr, ?_⟩
  intro S gamma tau htau hle hgamma hstart halt
  apply hbound S gamma tau htau hle hgamma
  rcases halt with hlong | hfar
  · exact Or.inl hlong
  · right
    apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal r + ENNReal.ofReal r = ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hr.le hr.le]
        congr 1
        ring
      _ ≤ riemannianEDistOf StandardCap.metric 0 (gamma tau) := hfar
      _ ≤ riemannianEDistOf StandardCap.metric 0 (gamma 0) +
          riemannianEDistOf StandardCap.metric (gamma 0) (gamma tau) :=
        riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal r + riemannianEDistOf StandardCap.metric (gamma 0) (gamma tau) :=
        add_le_add hstart le_rfl

end DifferentialGeometry.PDE.RicciFlow

end
