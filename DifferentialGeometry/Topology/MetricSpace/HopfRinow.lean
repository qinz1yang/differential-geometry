import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint
import DifferentialGeometry.Topology.MetricSpace.ApproximateMidpoint
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_radial_trimming_of_arbitrarily_short_curves
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p y : X) {r δ η : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hy : dist y p ≤ r + δ) :
    ∃ z : X, dist z p ≤ r ∧ dist y z < δ + η := by
  by_cases hyr : dist y p ≤ r
  · exact ⟨y, hyr, by simpa using add_pos_of_nonneg_of_pos hδ hη⟩
  obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves p y η hη
  have hrange : r ∈ Icc (dist p (c 0)) (dist p (c 1)) := by
    rw [hc0, hc1, dist_self]
    exact ⟨hr, by rw [dist_comm]; exact (lt_of_not_ge hyr).le⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1
    (continuous_const.dist hc : Continuous fun t => dist p (c t)) hrange
  change dist p (c t) = r at ht
  have hbound := (edist_add_edist_le_eVariationOn c t).trans_lt hlen
  rw [hc0, hc1, edist_dist, edist_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hbound
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (add_pos_of_nonneg_of_pos dist_nonneg hη)).mp hbound
  refine ⟨c t, by rw [dist_comm, ht], ?_⟩
  rw [dist_comm y (c t), dist_comm y p] at *
  linarith

theorem exists_larger_isCompact_closedBall_of_arbitrarily_short_curves
    [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {r : ℝ} (hr : 0 ≤ r) (hcompact : IsCompact (closedBall p r)) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (closedBall p (r + δ)) := by
  obtain ⟨δ, hδ, hthick⟩ := hcompact.exists_isCompact_cthickening
  refine ⟨δ / 3, by positivity, hthick.of_isClosed_subset isClosed_closedBall ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := exists_radial_trimming_of_arbitrarily_short_curves
    hcurves p y hr (by positivity : 0 ≤ δ / 3) (by positivity : 0 < δ / 3) hy
  apply thickening_subset_cthickening δ (closedBall p r)
  exact mem_thickening_iff.mpr ⟨z, hz, by linarith⟩

theorem properSpace_of_arbitrarily_short_curves [CompleteSpace X] [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) : ProperSpace X := by
  refine ⟨fun p R => ?_⟩
  let S : Set ℝ := {r | 0 < r ∧ IsCompact (closedBall p r)}
  obtain ⟨r₀, hr₀, hcompact₀⟩ := exists_isCompact_closedBall p
  have hS : S.Nonempty := ⟨r₀, hr₀, hcompact₀⟩
  by_cases hbounded : BddAbove S
  · have hsup : 0 < sSup S := hr₀.trans_le (le_csSup hbounded ⟨hr₀, hcompact₀⟩)
    have hcompact : IsCompact (closedBall p (sSup S)) := by
      apply isCompact_iff_totallyBounded_isComplete.mpr
      refine ⟨?_, isClosed_closedBall.isComplete⟩
      rw [totallyBounded_iff]
      intro ε hε
      obtain ⟨r, hr, hnear⟩ := exists_lt_of_lt_csSup hS
        (by linarith : sSup S - ε / 4 < sSup S)
      have hrsup : r ≤ sSup S := le_csSup hbounded hr
      obtain ⟨T, hTfinite, hTcover⟩ := totallyBounded_iff.mp hr.2.totallyBounded
        (ε / 2) (half_pos hε)
      refine ⟨T, hTfinite, fun y hy => ?_⟩
      obtain ⟨z, hz, hyz⟩ := exists_radial_trimming_of_arbitrarily_short_curves
        hcurves p y hr.1.le (sub_nonneg.mpr hrsup) (by positivity : 0 < ε / 4)
        (by simpa only [add_sub_cancel] using (show dist y p ≤ sSup S from hy))
      obtain ⟨w, hwT, hzw⟩ := mem_iUnion₂.mp (hTcover hz)
      refine mem_iUnion₂.mpr ⟨w, hwT, ?_⟩
      change dist y w < ε
      change dist z w < ε / 2 at hzw
      linarith [dist_triangle y z w]
    obtain ⟨δ, hδ, hlarge⟩ :=
      exists_larger_isCompact_closedBall_of_arbitrarily_short_curves hcurves p hsup.le hcompact
    have hle := le_csSup hbounded (show sSup S + δ ∈ S from ⟨by linarith, hlarge⟩)
    exact False.elim (by linarith)
  · obtain ⟨r, hr, hRr⟩ := not_bddAbove_iff.mp hbounded R
    exact hr.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hRr.le)

theorem properSpace_of_approximate_midpoints [CompleteSpace X] [LocallyCompactSpace X]
    (hmid : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ z : X, dist a z ≤ dist a b / 2 + ε ∧ dist b z ≤ dist a b / 2 + ε) :
    ProperSpace X := by
  apply properSpace_of_arbitrarily_short_curves
  intro a b ε hε
  obtain ⟨c, hc, hc0, hc1, _, hlen⟩ :=
    exists_curve_eVariationOn_lt_of_approximate_midpoints hmid a b hε
  exact ⟨c, hc, hc0, hc1, hlen⟩

theorem exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves
    [CompleteSpace X] [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) (a b : X) :
    ∃ f : Icc (0 : ℝ) 1 → X, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  let : ProperSpace X := properSpace_of_arbitrarily_short_curves hcurves
  exact exists_metric_segment_of_approximate_midpoints
    (approximate_midpoints_of_arbitrarily_short_curves hcurves) a b

end Metric
