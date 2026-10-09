import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

theorem scale_ratio_of_support_meeting {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z)
    {R C : ℝ} (hC : 0 ≤ C) (hbudget : Λ * max R C ≤ 1 / 4)
    (hmeet : (closedBall z (C * ρ z) ∩ ball p (R * ρ p)).Nonempty) :
    ρ z / ρ p ∈ Icc (1 / 2) 2 ∧ dist z p ≤ (R + 2 * C) * ρ p := by
  obtain ⟨q, hqz, hqp⟩ := hmeet
  have hd : dist z p ≤ R * ρ p + C * ρ z := by
    have ht := dist_triangle z q p
    rw [dist_comm z q] at ht
    change dist q z ≤ C * ρ z at hqz
    change dist q p < R * ρ p at hqp
    linarith
  have hR : Λ * R ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (le_max_left R C) (NNReal.coe_nonneg Λ)).trans hbudget
  have hC' : Λ * C ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (le_max_right R C) (NNReal.coe_nonneg Λ)).trans hbudget
  have hlip := hρ.dist_le_mul z p
  rw [Real.dist_eq] at hlip
  have hsmall : |ρ z - ρ p| ≤ (ρ p + ρ z) / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg Λ)
    have h2 := mul_le_mul_of_nonneg_right hR hp.le
    have h3 := mul_le_mul_of_nonneg_right hC' hz.le
    nlinarith
  have hlow : ρ p / 2 ≤ ρ z := by linarith [(abs_le.mp hsmall).1]
  have hhigh : ρ z ≤ 2 * ρ p := by linarith [(abs_le.mp hsmall).2]
  refine ⟨⟨(le_div_iff₀ hp).mpr (by linarith), (div_le_iff₀ hp).mpr hhigh⟩, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hhigh hC]

theorem enlarged_core_ball_subset_of_supports_meeting {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z w : X}
    (hp : 0 < ρ p) (hz : 0 < ρ z) (hw : 0 < ρ w)
    {R C a : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : Λ * max R C ≤ 1 / 4)
    (hzmeet : (closedBall z (C * ρ z) ∩ ball p (R * ρ p)).Nonempty)
    (hwmeet : (closedBall w (C * ρ w) ∩ ball p (R * ρ p)).Nonempty) :
    ball z (a * ρ z) ⊆ ball w ((4 * (R + 2 * C + a)) * ρ w) := by
  have hbz := scale_ratio_of_support_meeting hρ hp hz hC hbudget hzmeet
  have hbw := scale_ratio_of_support_meeting hρ hp hw hC hbudget hwmeet
  have hhigh : ρ z ≤ 2 * ρ p := (div_le_iff₀ hp).mp hbz.1.2
  have hlow : ρ p ≤ 2 * ρ w := by
    have hh := (le_div_iff₀ hp).mp hbw.1.1
    linarith
  intro x hx
  have ht1 := dist_triangle z p w
  rw [dist_comm p w] at ht1
  have ht2 := dist_triangle x z w
  change dist x z < a * ρ z at hx
  change dist x w < (4 * (R + 2 * C + a)) * ρ w
  have h1 := mul_le_mul_of_nonneg_left hhigh ha
  have h2 := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * (R + 2 * C + a) by positivity)
  nlinarith [hbz.2, hbw.2]

end GC.MetricGeometry
