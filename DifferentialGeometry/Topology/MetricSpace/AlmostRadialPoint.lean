import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_first_dist_eq_of_continuous_curve
    {p : X} {t : ℝ} (c : unitInterval → X) (hc : Continuous c)
    (hc0 : c 0 = p) (ht : 0 ≤ t) (ht1 : t ≤ dist p (c 1)) :
    ∃ s : unitInterval, dist p (c s) = t ∧ ∀ v ≤ s, dist p (c v) ≤ t := by
  have hd : Continuous (fun v => dist p (c v)) := continuous_const.dist hc
  have hrange : t ∈ Icc (dist p (c 0)) (dist p (c 1)) := by
    rw [hc0, dist_self]
    exact ⟨ht, ht1⟩
  obtain ⟨v, hv⟩ := intermediate_value_univ (0 : unitInterval) 1 hd hrange
  obtain ⟨s, hs, hleast⟩ := (isClosed_eq hd continuous_const).isCompact.exists_isLeast ⟨v, hv⟩
  refine ⟨s, hs, ?_⟩
  intro v hvs
  by_contra h
  have htv : t < dist p (c v) := lt_of_not_ge h
  obtain ⟨w, hw, hwt⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ v from unitInterval.nonneg')
    hd.continuousOn (show t ∈ Icc (dist p (c 0)) (dist p (c v)) by
      rw [hc0, dist_self]; exact ⟨ht, htv.le⟩)
  have hsw : s ≤ w := hleast hwt
  have hveq : v = s := le_antisymm hvs (hsw.trans hw.2)
  subst v
  exact (ne_of_gt htv) hs

theorem exists_almost_radial_point_of_curve
    {p u : X} {t η : ℝ} (c : unitInterval → X) (hc : Continuous c)
    (hc0 : c 0 = p) (hc1 : c 1 = u) (ht : 0 ≤ t) (htr : t ≤ dist p u)
    (hη : 0 < η) (hlen : eVariationOn c univ < ENNReal.ofReal (dist p u + η)) :
    ∃ s : unitInterval, dist p (c s) = t ∧
      dist p u - t ≤ dist (c s) u ∧ dist (c s) u < dist p u - t + η ∧
      ∀ v ≤ s, c v ∈ closedBall p t := by
  obtain ⟨s, hs, hbefore⟩ := exists_first_dist_eq_of_continuous_curve c hc hc0 ht
    (by simpa only [hc1] using htr)
  have hbound := (edist_add_edist_le_eVariationOn c s).trans_lt hlen
  rw [hc0, hc1, edist_dist, edist_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hbound
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (add_pos_of_nonneg_of_pos dist_nonneg hη)).mp hbound
  refine ⟨s, hs, ?_, by linarith, ?_⟩
  · linarith [dist_triangle p (c s) u]
  · intro v hvs
    rw [mem_closedBall, dist_comm]
    exact hbefore v hvs

theorem exists_almost_radial_point_of_arbitrarily_short_curves
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    (p u : X) {t η : ℝ} (ht : 0 ≤ t) (htr : t ≤ dist p u) (hη : 0 < η) :
    ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
      eVariationOn c univ < ENNReal.ofReal (dist p u + η) ∧
      ∃ s : unitInterval, dist p (c s) = t ∧
        dist p u - t ≤ dist (c s) u ∧ dist (c s) u < dist p u - t + η ∧
        ∀ v ≤ s, c v ∈ closedBall p t := by
  obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves p u η hη
  exact ⟨c, hc, hc0, hc1, hlen,
    exists_almost_radial_point_of_curve c hc hc0 hc1 ht htr hη hlen⟩

end Metric
