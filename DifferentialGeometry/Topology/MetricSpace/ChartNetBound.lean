import DifferentialGeometry.Topology.MetricSpace.RadialChartNet

set_option autoImplicit false

open Real

namespace Metric

theorem chart_net_bound_mono_dimension {m n : ℕ} (hmn : m ≤ n)
    {L R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    (1 + ⌈4 * L ^ 2 * sqrt m * sinh (2 * R) / ε⌉₊) ^ m ≤
      (1 + ⌈4 * L ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n := by
  have hs : sqrt (m : ℝ) ≤ sqrt (n : ℝ) := sqrt_le_sqrt (by exact_mod_cast hmn)
  have hc : 4 * L ^ 2 * sqrt m * sinh (2 * R) / ε ≤
      4 * L ^ 2 * sqrt n * sinh (2 * R) / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (sinh_nonneg_iff.mpr (by positivity))
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_left (Nat.ceil_mono hc) 1) m).trans
    (Nat.pow_le_pow_right (by omega) hmn)

end Metric
