import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

namespace DifferentialGeometry

theorem ball_subset_eball_ofReal {α : Type*} [PseudoMetricSpace α]
    (x : α) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r ⊆ Metric.eball x (ENNReal.ofReal r) := by
  intro y hy
  rw [Metric.mem_ball] at hy
  rw [Metric.mem_eball, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hy

theorem closedEBall_ofReal_subset_ball {α : Type*} [PseudoMetricSpace α]
    (x : α) {r R : ℝ} (hr : 0 ≤ r) (hR : r < R) :
    Metric.closedEBall x (ENNReal.ofReal r) ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_closedEBall] at hy
  rw [edist_dist] at hy
  rw [Metric.mem_ball]
  have hdist_le : dist y x ≤ r := by
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 hy
  exact lt_of_le_of_lt hdist_le hR

end DifferentialGeometry
