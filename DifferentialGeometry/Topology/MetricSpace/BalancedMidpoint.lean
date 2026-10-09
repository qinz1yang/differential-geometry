import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint

set_option autoImplicit false

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_balanced_midpoint_of_curve {x y : X} {η : ℝ} (hη : 0 < η)
    (c : unitInterval → X) (hc : Continuous c) (hc0 : c 0 = x) (hc1 : c 1 = y)
    (hlen : eVariationOn c univ < ENNReal.ofReal (dist x y + η)) :
    ∃ t : unitInterval, dist x (c t) = dist y (c t) ∧
      dist x y / 2 ≤ dist x (c t) ∧ dist x (c t) < (dist x y + η) / 2 := by
  obtain ⟨t, ht⟩ := intermediate_value_univ₂
    (a := (0 : unitInterval)) (b := (1 : unitInterval))
    (continuous_const.dist hc : Continuous fun s => dist x (c s))
    (continuous_const.dist hc : Continuous fun s => dist y (c s))
    (by simp [hc0]) (by simp [hc1])
  have hbound := (edist_add_edist_le_eVariationOn c t).trans_lt hlen
  rw [hc0, hc1, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hbound
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (add_pos_of_nonneg_of_pos dist_nonneg hη)).mp hbound
  have htri := dist_triangle x (c t) y
  rw [dist_comm (c t) y, ← ht] at hreal htri
  exact ⟨t, ht, by linarith, by linarith⟩

theorem exists_balanced_midpoint_of_arbitrarily_short_curves
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (x y : X) {ν : ℝ} (hν : 0 < ν) (hxy : 0 < dist x y) :
    ∃ z : X, dist x z = dist y z ∧ dist x y / 2 ≤ dist x z ∧
      dist x z < (1 + ν) * dist x y / 2 := by
  obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves x y (ν * dist x y) (mul_pos hν hxy)
  obtain ⟨t, heq, hlo, hup⟩ := exists_balanced_midpoint_of_curve (mul_pos hν hxy) c hc hc0 hc1 hlen
  exact ⟨c t, heq, hlo, by nlinarith⟩

end Metric
