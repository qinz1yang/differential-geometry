import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

theorem support_meeting_ball_buffer {p q : X} {r rj L c b : ℝ} {S U : Set X}
    (hr : 0 < r) (hrj : 0 < rj) (hL : 0 < L)
    (hratio : (1 / 2 : ℝ) ≤ rj / r) (hgap : 4 * L < b - c)
    (hsupport : S ⊆ closedBall q (c * rj)) (hdomain : ball q (b * rj) ⊆ U)
    (hmeet : (S ∩ ball p (L * r)).Nonempty) :
    ball p (L * r) ⊆ ball q ((c + 4 * L) * rj) ∧
      ball q ((c + 4 * L) * rj) ⊆ U ∧
      ∀ x ∈ ball p (L * r), Uᶜ.Nonempty → (b - c - 4 * L) * rj ≤ infDist x Uᶜ := by
  obtain ⟨z, hzS, hz⟩ := hmeet
  have hzq : dist z q ≤ c * rj := hsupport hzS
  have hrcomp : r ≤ 2 * rj := by
    have hh := (le_div_iff₀ hr).mp hratio
    linarith
  have hsub : ball p (L * r) ⊆ ball q ((c + 4 * L) * rj) := by
    intro x hx
    have h1 := dist_triangle x p z
    have h2 := dist_triangle x z q
    rw [dist_comm p z] at h1
    change dist x p < L * r at hx
    change dist z p < L * r at hz
    change dist x q < (c + 4 * L) * rj
    nlinarith [mul_le_mul_of_nonneg_left hrcomp hL.le]
  have hU : ball q ((c + 4 * L) * rj) ⊆ U := by
    apply Subset.trans _ hdomain
    exact ball_subset_ball (mul_le_mul_of_nonneg_right (by linarith : c + 4 * L ≤ b) hrj.le)
  refine ⟨hsub, hU, ?_⟩
  intro x hx hne
  apply (le_infDist hne).mpr
  intro y hy
  have hxy : dist x q < (c + 4 * L) * rj := hsub hx
  have hyq : b * rj ≤ dist y q := by
    by_contra! h
    exact hy (hdomain h)
  have ht := dist_triangle y x q
  rw [dist_comm y x] at ht
  nlinarith

end GC.MetricGeometry
