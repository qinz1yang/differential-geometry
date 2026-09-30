import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

noncomputable section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

theorem exists_weighted_point_selection {f : X → ℝ} {p y : X} {R eta : ℝ}
    (hcompact : IsCompact (closedBall p R)) (hf : ContinuousOn f (closedBall p R))
    (hy : dist p y < R) (hfy : 0 < f y) (heta : eta < 1) :
    ∃ x : X, dist p x < R ∧ 0 < f x ∧
      f y * (R - dist p y) ^ 2 ≤ f x * (R - dist p x) ^ 2 ∧
      ∀ z : X, dist x z ≤ eta * (R - dist p x) →
        dist p z < R ∧ f z ≤ ((1 - eta)⁻¹) ^ 2 * f x := by
  let F : X → ℝ := fun z => f z * (R - dist p z) ^ 2
  have hF : ContinuousOn F (closedBall p R) :=
    hf.mul ((continuous_const.sub (continuous_const.dist continuous_id)).pow 2).continuousOn
  have hyball : y ∈ closedBall p R := by
    simpa only [mem_closedBall, dist_comm] using hy.le
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn ⟨y, hyball⟩ hF
  have hxle : dist p x ≤ R := by simpa only [mem_closedBall, dist_comm] using hx
  have hweight : f y * (R - dist p y) ^ 2 ≤ f x * (R - dist p x) ^ 2 := hmax hyball
  have hpositive : 0 < f y * (R - dist p y) ^ 2 :=
    mul_pos hfy (sq_pos_of_pos (sub_pos.mpr hy))
  have hxlt : dist p x < R := by
    by_contra hn
    have hz : R - dist p x = 0 := sub_eq_zero.mpr (le_antisymm (le_of_not_gt hn) hxle)
    rw [hz, zero_pow (by decide), mul_zero] at hweight
    exact (not_le_of_gt hpositive) hweight
  have hsigma : 0 < R - dist p x := sub_pos.mpr hxlt
  have hfx : 0 < f x :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos hsigma)).mp (hpositive.trans_le hweight)
  refine ⟨x, hxlt, hfx, hweight, ?_⟩
  intro z hz
  have hslack : (1 - eta) * (R - dist p x) ≤ R - dist p z := by
    have htri := dist_triangle p x z
    nlinarith
  have hslack_pos : 0 < (1 - eta) * (R - dist p x) :=
    mul_pos (sub_pos.mpr heta) hsigma
  have hzlt : dist p z < R := by linarith
  refine ⟨hzlt, ?_⟩
  by_cases hfz : 0 ≤ f z
  · have hzball : z ∈ closedBall p R := by
      simpa only [mem_closedBall, dist_comm] using hzlt.le
    have hsquare : ((1 - eta) * (R - dist p x)) ^ 2 ≤ (R - dist p z) ^ 2 :=
      (sq_le_sq₀ hslack_pos.le (hslack_pos.le.trans hslack)).mpr hslack
    have hprod := mul_le_mul_of_nonneg_left hsquare hfz
    have hmaxz : f z * (R - dist p z) ^ 2 ≤ f x * (R - dist p x) ^ 2 := hmax hzball
    have hcancel : f z * (1 - eta) ^ 2 ≤ f x := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hsigma)).mp
      nlinarith [hprod, hmaxz]
    have hdiv : f z ≤ f x / (1 - eta) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr heta))).mpr hcancel
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hdiv
  · exact (le_of_lt (lt_of_not_ge hfz)).trans (mul_nonneg (sq_nonneg _) hfx.le)

end Metric
