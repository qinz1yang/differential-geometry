import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Compact

/-!
# CH12-O8, package P4a: openness from a local descent inequality (compact minimisation)

If `f : X → V` is continuous on a compact closed ball `closedBall q ρ` and at every point
`z` of the open ball with `f z ≠ w` there is a point `y` of the open ball with
`‖f y - w‖ + κ d(z, y) < ‖f z - w‖`, then `w` has a preimage within `‖f q - w‖ / κ` of `q`,
provided `‖f q - w‖ < κ ρ`.  (Minimise `‖f z - w‖ + κ d(z, q)` on the closed ball.)
This replaces the Lyusternik iteration for the sharp `(1 - τ)` image bound in KL 83.1.
-/

set_option autoImplicit false

open Set Metric

namespace GC.LongTime.Ch12

theorem exists_preimage_of_local_descent_O8 {X V : Type*} [MetricSpace X]
    [NormedAddCommGroup V] {f : X → V} {q : X} {ρ κ : ℝ} {w : V}
    (hκ : 0 < κ) (hK : IsCompact (closedBall q ρ))
    (hf : ContinuousOn f (closedBall q ρ))
    (hstart : ‖f q - w‖ < κ * ρ)
    (hdescent : ∀ z ∈ ball q ρ, f z ≠ w →
      ∃ y ∈ ball q ρ, ‖f y - w‖ + κ * dist z y < ‖f z - w‖) :
    ∃ z ∈ ball q ρ, f z = w ∧ dist q z ≤ ‖f q - w‖ / κ := by
  set Φ : X → ℝ := fun z => ‖f z - w‖ + κ * dist z q with hΦ
  have hΦc : ContinuousOn Φ (closedBall q ρ) :=
    ((hf.sub continuousOn_const).norm).add (continuousOn_const.mul
      (continuous_id.dist continuous_const).continuousOn)
  have hρ : 0 ≤ ρ := by
    by_contra h
    have : κ * ρ < 0 := mul_neg_of_pos_of_neg hκ (lt_of_not_ge h)
    linarith [norm_nonneg (f q - w)]
  have hq : q ∈ closedBall q ρ := mem_closedBall_self hρ
  obtain ⟨z, hz, hzmin⟩ := hK.exists_isMinOn ⟨q, hq⟩ hΦc
  have hΦz : Φ z ≤ Φ q := hzmin hq
  have hΦq : Φ q = ‖f q - w‖ := by simp [hΦ]
  have hdist : κ * dist z q ≤ ‖f q - w‖ := by
    have : ‖f z - w‖ + κ * dist z q ≤ ‖f q - w‖ := hΦz.trans_eq hΦq
    linarith [norm_nonneg (f z - w)]
  have hzball : z ∈ ball q ρ := by
    rw [mem_ball]
    have : κ * dist z q < κ * ρ := lt_of_le_of_lt hdist hstart
    exact lt_of_mul_lt_mul_left this hκ.le
  have hfz : f z = w := by
    by_contra hne
    obtain ⟨y, hy, hdesc⟩ := hdescent z hzball hne
    have hyK : y ∈ closedBall q ρ := ball_subset_closedBall hy
    have hmin := hzmin hyK
    change Φ z ≤ Φ y at hmin
    simp only [hΦ] at hmin
    have htri : dist y q ≤ dist z y + dist z q := by
      rw [dist_comm z y]; exact dist_triangle y z q
    nlinarith
  refine ⟨z, hzball, hfz, ?_⟩
  rw [dist_comm, le_div_iff₀ hκ, mul_comm]
  exact hdist

end GC.LongTime.Ch12
