import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_displacement_le_of_derivative_comparison {P : E → E} {s : Set E}
    (hs : Convex ℝ s) (hP : ∀ z ∈ s, DifferentiableAt ℝ P z)
    (Q : E →L[ℝ] E) (hQ : ‖Q - ContinuousLinearMap.id ℝ E‖ ≤ 1)
    {ε : ℝ} (hderiv : ∀ z ∈ s, ‖fderiv ℝ P z - Q‖ ≤ ε)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖P y - y‖ ≤ ‖P x - x‖ + (1 + ε) * ‖y - x‖ := by
  have hd (z : E) (hz : z ∈ s) :
      HasFDerivAt (fun z => P z - z) (fderiv ℝ P z - ContinuousLinearMap.id ℝ E) z :=
    (hP z hz).hasFDerivAt.sub (hasFDerivAt_id z)
  have hbound (z : E) (hz : z ∈ s) :
      ‖fderiv ℝ (fun z => P z - z) z‖ ≤ 1 + ε := by
    rw [(hd z hz).fderiv]
    have hh := norm_add_le (fderiv ℝ P z - Q) (Q - ContinuousLinearMap.id ℝ E)
    rw [sub_add_sub_cancel] at hh
    linarith [hderiv z hz]
  have hh := hs.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hd z hz).differentiableAt) hbound hx hy
  have ht := norm_sub_le ((P y - y) - (P x - x)) (-(P x - x))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  linarith

theorem perturbed_projection_on_original_ball {P : E → E} {x y : E}
    {ρ σ r ε e : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hrlo : (3 / 5 : ℝ) * σ * ρ ≤ r) (hrhi : r ≤ (5 / 3 : ℝ) * σ * ρ)
    (he : e ≤ 3 * σ / 10) (hxy : ‖y - x‖ ≤ e * ρ)
    (Q : E →L[ℝ] E) (hQ : ‖Q - ContinuousLinearMap.id ℝ E‖ ≤ 1)
    (hP : ∀ z ∈ ball x r, DifferentiableAt ℝ P z)
    (hderiv : ∀ z ∈ ball x r, ‖fderiv ℝ P z - Q‖ ≤ ε)
    (hbase : ‖P x - x‖ ≤ ε * r) :
    ‖y - x‖ ≤ r / 2 ∧ ball y (r / 2) ⊆ ball x r ∧
      segment ℝ x y ⊆ ball x r ∧
      ‖P y - y‖ ≤ ((5 / 3 : ℝ) * ε * σ + (1 + ε) * e) * ρ := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrlo
  have hbudget := mul_le_mul_of_nonneg_right he hρ.le
  have hhalf : ‖y - x‖ ≤ r / 2 := by nlinarith
  have hx : x ∈ ball x r := mem_ball_self hr
  have hy : y ∈ ball x r := by rw [mem_ball, dist_eq_norm]; linarith
  refine ⟨hhalf, ?_, (convex_ball x r).segment_subset hx hy, ?_⟩
  · intro z hz
    have hh := dist_triangle z y x
    have hz' : dist z y < r / 2 := hz
    rw [dist_eq_norm y x] at hh
    change dist z x < r
    linarith
  · have hh := norm_displacement_le_of_derivative_comparison (convex_ball x r)
      hP Q hQ hderiv hx hy
    have h1 := mul_le_mul_of_nonneg_left hrhi hε
    have h2 := mul_le_mul_of_nonneg_left hxy (by linarith : 0 ≤ 1 + ε)
    nlinarith

end DifferentialGeometry.Analysis
