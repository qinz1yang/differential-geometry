import DifferentialGeometry.Geometry.Metric.ConeAngularMidpoint
import DifferentialGeometry.Topology.MetricSpace.RestrictedGeodesicMidpoint

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

theorem exists_base_segment_of_cone_segments
    {Y : Type*} [MetricSpace Y] [ProperSpace Y]
    (hsegments : ∀ a b : EuclideanCone Y, ∃ f : Icc (0 : ℝ) 1 → EuclideanCone Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (a b : Y) (hab : dist a b < Real.pi) :
    ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  apply exists_metric_segment_of_midpoints_lt Real.pi_pos _ a b hab
  intro u v huv
  obtain ⟨g, _, hg0, hg1, hgd⟩ := hsegments (mk 1 u) (mk 1 v)
  let z := g ⟨1 / 2, by norm_num⟩
  have hu : dist (mk 1 u) z = dist (mk 1 u) (mk 1 v) / 2 := by
    have h := hgd ⟨0, by norm_num⟩ ⟨1 / 2, by norm_num⟩
    rw [hg0] at h
    change dist (mk 1 u) z = dist (mk 1 u) (mk 1 v) * |(0 : ℝ) - 1 / 2| at h
    norm_num at h
    simpa only [div_eq_mul_inv, one_mul, dist_mk, NNReal.coe_one] using h
  have hv : dist (mk 1 v) z = dist (mk 1 u) (mk 1 v) / 2 := by
    have h := hgd ⟨1, by norm_num⟩ ⟨1 / 2, by norm_num⟩
    rw [hg1] at h
    change dist (mk 1 v) z = dist (mk 1 u) (mk 1 v) * |(1 : ℝ) - 1 / 2| at h
    norm_num at h
    simpa only [div_eq_mul_inv, one_mul, dist_mk, NNReal.coe_one] using h
  obtain ⟨_, w, _, huw, hvw⟩ := exists_angular_midpoint_of_cone_midpoint huv z hu hv
  exact ⟨w, huw, by simpa only [dist_comm w v] using hvw⟩

end Metric.EuclideanCone
