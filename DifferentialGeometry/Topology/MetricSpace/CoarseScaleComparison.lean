import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

theorem coarse_scale_comparison_of_support_meeting
    {x₀ xᵢ v : X} {r₀ rᵢ C ℓ : ℝ}
    (hr₀ : 0 < r₀) (hrᵢ : 0 < rᵢ) (hC : 0 ≤ C) (hℓ : 0 ≤ ℓ)
    (hbudget : C * ℓ ≤ 1 / 100)
    (hforward : rᵢ - r₀ ≤ C * (dist xᵢ x₀ + r₀))
    (hreverse : r₀ - rᵢ ≤ C * (dist xᵢ x₀ + rᵢ))
    (hv : v ∈ ball x₀ (5 * ℓ * r₀))
    (hmeet : (closedBall xᵢ (20 * ℓ * rᵢ) ∩ ball v (ℓ * r₀)).Nonempty) :
    r₀ / (2 * (C + 1)) ≤ rᵢ ∧ rᵢ ≤ 2 * (C + 1) * r₀ ∧
      dist xᵢ x₀ ≤ (20 * (2 * (C + 1)) + 6) * ℓ * r₀ := by
  obtain ⟨q, hqi, hqv⟩ := hmeet
  change dist q xᵢ ≤ 20 * ℓ * rᵢ at hqi
  change dist q v < ℓ * r₀ at hqv
  change dist v x₀ < 5 * ℓ * r₀ at hv
  have hdist : dist xᵢ x₀ ≤ 20 * ℓ * rᵢ + 6 * ℓ * r₀ := by
    have htriangle₁ := dist_triangle xᵢ q x₀
    have htriangle₂ := dist_triangle q v x₀
    rw [dist_comm xᵢ q] at htriangle₁
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hdist hC
  have hbudget₀ := mul_le_mul_of_nonneg_right hbudget hr₀.le
  have hbudgetᵢ := mul_le_mul_of_nonneg_right hbudget hrᵢ.le
  have hsmall : C * dist xᵢ x₀ ≤ (rᵢ + r₀) / 4 := by
    nlinarith
  have hCr₀ : 0 ≤ C * r₀ := mul_nonneg hC hr₀.le
  have hCrᵢ : 0 ≤ C * rᵢ := mul_nonneg hC hrᵢ.le
  have hhigh : rᵢ ≤ 2 * (C + 1) * r₀ := by
    nlinarith [hforward]
  have hlow : r₀ ≤ 2 * (C + 1) * rᵢ := by
    nlinarith [hreverse]
  refine ⟨(div_le_iff₀ (by positivity : 0 < 2 * (C + 1))).mpr ?_, hhigh, ?_⟩
  · nlinarith [hlow]
  · have hscaled_high := mul_le_mul_of_nonneg_left hhigh
      (show 0 ≤ 20 * ℓ by positivity)
    nlinarith [hdist]

end Metric
