import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ContinuousLinearMap

variable {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_on_segment_le_of_vanishing_at_small_scale
    (J : H →L[ℝ] V) (hJ : ‖J‖ ≤ 1) {x y : H} (hx : J x = 0)
    {ρ R c e : ℝ} (hR : 0 ≤ R) (hc : 0 < c)
    (herror : ‖y - x‖ ≤ e * ρ) (hsmall : R < ρ / c → J y = 0)
    (he : 0 ≤ e) : ∀ z ∈ segment ℝ x y, ‖J z‖ ≤ c * e * R := by
  have hy : ‖J y‖ ≤ c * e * R := by
    by_cases h : R < ρ / c
    · rw [hsmall h, norm_zero]
      positivity
    · have hρ : ρ ≤ c * R := by
        have hh := le_of_not_gt h
        rw [div_le_iff₀ hc] at hh
        nlinarith
      have hbound : ‖J y‖ ≤ e * ρ := by
        have hid : J (y - x) = J y := by rw [map_sub, hx, sub_zero]
        rw [← hid]
        exact ((J.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hJ)).trans herror
      exact hbound.trans (by nlinarith [mul_le_mul_of_nonneg_left hρ he])
  intro z hz
  have hconv : Convex ℝ {v : H | ‖J v‖ ≤ c * e * R} :=
    by simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right, ContinuousLinearMap.coe_coe]
      using (convex_closedBall (0 : V) (c * e * R)).linear_preimage J.toLinearMap
  apply hconv.segment_subset ?_ hy hz
  simpa only [Set.mem_ofPred_eq, hx, norm_zero] using (show 0 ≤ c * e * R by positivity)

end ContinuousLinearMap
