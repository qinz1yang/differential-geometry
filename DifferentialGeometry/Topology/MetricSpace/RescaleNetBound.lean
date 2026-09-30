import DifferentialGeometry.Topology.MetricSpace.ChartNetBound
import DifferentialGeometry.Analysis.Convex.HyperbolicSine

set_option autoImplicit false

open Real

namespace Metric

theorem chart_net_bound_rescale_le {n : ℕ} {L R ε c : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1) :
    (1 + ⌈4 * L ^ 2 * sqrt n * sinh (2 * (c * R)) / (c * ε)⌉₊) ^ n ≤
      (1 + ⌈4 * L ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n := by
  have hs : sinh (2 * (c * R)) ≤ c * sinh (2 * R) := by
    have heq : 2 * (c * R) = c * (2 * R) := by ring
    rw [heq]
    exact sinh_mul_le_mul_sinh ⟨hc.le, hc1⟩ (by positivity : 0 ≤ 2 * R)
  have ht : 4 * L ^ 2 * sqrt n * sinh (2 * (c * R)) / (c * ε) ≤
      4 * L ^ 2 * sqrt n * (c * sinh (2 * R)) / (c * ε) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
  have heq : 4 * L ^ 2 * sqrt n * (c * sinh (2 * R)) / (c * ε) =
      4 * L ^ 2 * sqrt n * sinh (2 * R) / ε := by field_simp
  rw [heq] at ht
  exact Nat.pow_le_pow_left (Nat.add_le_add_left (Nat.ceil_mono ht) 1) n

end Metric
