import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped NNReal

namespace DifferentialGeometry.Geometry.Metric

theorem dist_rays_le_of_near_common_point
    {X : Type*} [PseudoMetricSpace X] {c d : ℝ≥0 → X} {p z : X}
    (hc : Isometry c) (hd : Isometry d) (hc0 : c 0 = p) (hd0 : d 0 = p)
    (r s t : ℝ≥0) {D : ℝ} (hr : dist p z = r)
    (hs : dist (c s) z ≤ D) (ht : dist (d t) z ≤ D) :
    dist (c r) (d r) ≤ 4 * D := by
  have hcs : dist (c s) p = (s : ℝ) := by
    rw [← hc0, hc.dist_eq, NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]
  have hdt : dist (d t) p = (t : ℝ) := by
    rw [← hd0, hd.dist_eq, NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
  have hsr : |(s : ℝ) - r| ≤ D := by
    have hh := (abs_dist_sub_le (c s) z p).trans hs
    simpa only [hcs, dist_comm z p, hr] using hh
  have htr : |(t : ℝ) - r| ≤ D := by
    have hh := (abs_dist_sub_le (d t) z p).trans ht
    simpa only [hdt, dist_comm z p, hr] using hh
  have hcrs : dist (c r) (c s) ≤ D := by
    simpa only [hc.dist_eq, NNReal.dist_eq, abs_sub_comm] using hsr
  have hdtr : dist (d t) (d r) ≤ D := by
    simpa only [hd.dist_eq, NNReal.dist_eq] using htr
  have hzdt : dist z (d t) ≤ D := by simpa only [dist_comm] using ht
  calc
    dist (c r) (d r) ≤ dist (c r) z + dist z (d r) := dist_triangle _ _ _
    _ ≤ (dist (c r) (c s) + dist (c s) z) + (dist z (d t) + dist (d t) (d r)) :=
      add_le_add (dist_triangle _ _ _) (dist_triangle _ _ _)
    _ ≤ 4 * D := by linarith

end DifferentialGeometry.Geometry.Metric
