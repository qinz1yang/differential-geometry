import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalBlowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Analysis.Integration.Integral.LogarithmicLowerBound

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature
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

end DifferentialGeometry.PDE.RicciFlow
