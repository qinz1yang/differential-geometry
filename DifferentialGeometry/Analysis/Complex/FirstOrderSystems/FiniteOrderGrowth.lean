import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.FiniteOrder

set_option autoImplicit false
noncomputable section

open Filter Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem exists_power_norm_bounds_of_analytic_inverse_gauge
    {P : ℂ → V →L[ℂ] V} {ξ : ℂ → V} {a : ℂ} {n : ℕ∞ω}
    (hP : ContDiffAt ℝ n P a) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => (Ring.inverse (P z)) (ξ z)) a)
    (hgerm : ¬ ∀ᶠ z in 𝓝 a, ξ z = 0) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧
      ∀ z ∈ ball a r,
        c * ‖z - a‖ ^
            analyticOrderNatAt (fun w => (Ring.inverse (P w)) (ξ w)) a ≤ ‖ξ z‖ ∧
          ‖ξ z‖ ≤ C * ‖z - a‖ ^
            analyticOrderNatAt (fun w => (Ring.inverse (P w)) (ξ w)) a := by
  obtain ⟨_, G, _, _, hPG, hPGzero, hfactor⟩ :=
    exists_finite_order_factor_of_analytic_inverse_gauge hP hunit hF hgerm
  let m : ℕ := analyticOrderNatAt (fun w => (Ring.inverse (P w)) (ξ w)) a
  change ξ =ᶠ[𝓝 a] (fun z => (z - a) ^ m • P z (G z)) at hfactor
  have hPGTheta : (fun z => P z (G z)) =Θ[𝓝 a] (fun _ => (1 : ℂ)) :=
    hPG.continuousAt.isTheta hPGzero
  have hTheta : ξ =Θ[𝓝 a] (fun z => (z - a) ^ m) := by
    apply hfactor.trans_isTheta
    simpa only [smul_eq_mul, mul_one] using
      (Asymptotics.isTheta_refl (fun z => (z - a) ^ m) (𝓝 a)).smul hPGTheta
  obtain ⟨C, hC, hupper⟩ := Asymptotics.isBigO_iff'.mp hTheta.1
  obtain ⟨c, hc, hlower⟩ := Asymptotics.isBigO_iff''.mp hTheta.2
  have hbounds : ∀ᶠ z in 𝓝 a,
      c * ‖z - a‖ ^ m ≤ ‖ξ z‖ ∧ ‖ξ z‖ ≤ C * ‖z - a‖ ^ m := by
    filter_upwards [hlower, hupper] with z hzlower hzupper
    constructor
    · simpa only [norm_pow] using hzlower
    · simpa only [norm_pow] using hzupper
  obtain ⟨r, hr, hrbounds⟩ := Metric.eventually_nhds_iff_ball.mp hbounds
  exact ⟨c, C, r, hc, hC, hr, hrbounds⟩

end DifferentialGeometry.Analysis
