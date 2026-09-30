import DifferentialGeometry.Geometry.Metric.ZeroSupportIsolation
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

theorem radial_support_test_ball_buffer {ρ η : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z)
    {L T R e : ℝ} (hL : 0 < L) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 1600 * L ≤ T) (hR : T * ρ z ≤ R) (he : e < 1 / 40)
    (hlocal : dist z p ≤ 10 * R → T / 20 ≤ R / ρ p)
    {S : Set X} (herror : ∀ x ∈ S, |η x - dist z x / R| < e)
    (hsupport : ∀ x ∈ S, η x ∈ Icc (1 / 5) (9 / 10))
    (hmeet : (S ∩ ball p (L * ρ p)).Nonempty) :
    T / 20 ≤ R / ρ p ∧
      ∀ x ∈ ball p (L * ρ p), dist z x / R ∈ Icc (3 / 20) (19 / 20) := by
  have hT0 : 0 < T := by linarith
  have hR0 : 0 < R := (mul_pos hT0 hz).trans_le hR
  have hradial (x : X) (hx : x ∈ S) :
      7 / 40 < dist z x / R ∧ dist z x / R < 37 / 40 := by
    have ha := abs_lt.mp (herror x hx)
    have hb := hsupport x hx
    constructor <;> linarith [hb.1, hb.2]
  have hclosed : S ⊆ closedBall z ((37 / 40) * R) := by
    intro x hx
    rw [mem_closedBall, dist_comm]
    exact ((div_lt_iff₀ hR0).mp (hradial x hx).2).le
  have hpre := ball_subset_zero_core_of_support_meeting hρ hp hz hL
    (θ := 37 / 40) (by norm_num) hΛ (by linarith) (by norm_num; linarith)
    hR hlocal (hmeet.mono (inter_subset_inter_left _ hclosed))
  have hratio := hlocal (by linarith [hpre.1])
  have hratio' : T * ρ p ≤ 20 * R := by
    have hh := (le_div_iff₀ hp).mp hratio
    linarith
  have hmargin : 2 * L * ρ p ≤ R / 40 := by
    nlinarith [mul_le_mul_of_nonneg_right hT hp.le]
  refine ⟨hratio, ?_⟩
  obtain ⟨q, hqS, hqp⟩ := hmeet
  intro x hx
  have hqx : dist x q < 2 * L * ρ p := by
    have ht := dist_triangle x p q
    rw [dist_comm p q] at ht
    change dist x p < L * ρ p at hx
    change dist q p < L * ρ p at hqp
    linarith
  have hqlo := (lt_div_iff₀ hR0).mp (hradial q hqS).1
  have hqhi := (div_lt_iff₀ hR0).mp (hradial q hqS).2
  have h1 := dist_triangle z x q
  have h2 := dist_triangle z q x
  rw [dist_comm q x] at h2
  exact ⟨(le_div_iff₀ hR0).mpr (by linarith),
    (div_le_iff₀ hR0).mpr (by linarith)⟩

end GC.MetricGeometry
