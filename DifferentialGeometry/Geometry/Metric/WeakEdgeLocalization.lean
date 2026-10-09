import DifferentialGeometry.Geometry.Metric.SlowScaleQuotient
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

theorem strong_set_proximity_of_support_meeting {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z)
    {L Δ : ℝ} (hL : 0 < L) (hΔ : 120 * L ≤ Δ) (hsmall : Δ * Λ ≤ 1 / 100)
    {E : Set X} (hzE : z ∈ E)
    (hmeet : (closedBall z (20 * Δ * ρ z) ∩ ball p (L * ρ p)).Nonempty) :
    ρ z / ρ p < 63 / 50 ∧ infDist p E < 30 * Δ * ρ p := by
  have hΔ0 : 0 < Δ := by linarith
  have hLΛ : L * Λ ≤ 1 / 12000 := by
    have hh := mul_le_mul_of_nonneg_right hΔ (NNReal.coe_nonneg Λ)
    linarith
  obtain ⟨q, hqz, hqp⟩ := hmeet
  have hd : dist z p < 20 * Δ * ρ z + L * ρ p := by
    have ht := dist_triangle z q p
    rw [dist_comm z q] at ht
    change dist q z ≤ 20 * Δ * ρ z at hqz
    change dist q p < L * ρ p at hqp
    linarith
  have hlip := hρ.dist_le_mul z p
  rw [Real.dist_eq] at hlip
  have h1 := mul_le_mul_of_nonneg_left hd.le (NNReal.coe_nonneg Λ)
  have h2 := mul_le_mul_of_nonneg_right hsmall hz.le
  have h3 := mul_le_mul_of_nonneg_right hLΛ hp.le
  have hr : ρ z < 63 / 50 * ρ p := by nlinarith [(abs_le.mp hlip).2]
  refine ⟨(div_lt_iff₀ hp).mpr hr, ?_⟩
  have hnear := infDist_le_dist_of_mem hzE (x := p)
  rw [dist_comm p z] at hnear
  have h4 := mul_lt_mul_of_pos_left hr (show 0 < 20 * Δ by positivity)
  have h5 := mul_le_mul_of_nonneg_right hΔ hp.le
  nlinarith [mul_pos hΔ0 hp]

theorem weak_edge_quotient_alternative {P ρ : X → ℝ} {K Λ : NNReal}
    (hP : LipschitzWith K P) (hρ : LipschitzWith Λ ρ) (hK : (K : ℝ) ≤ 2)
    (hPnonneg : ∀ x, 0 ≤ P x) (hpos : ∀ x, 0 < ρ x)
    {p q : X} {L Δ : ℝ} (hL : 0 < L) (hΔ : 120 * L ≤ Δ)
    (hsmall : Δ * Λ ≤ 1 / 100) (hLsmall : L * Λ ≤ 1 / 4)
    (hq : q ∈ ball p (L * ρ p)) (hvq : P q / ρ q ≤ 9 * Δ)
    {E : Set X} (hnear : infDist p E ≤ 30 * Δ * ρ p) :
    (∀ x ∈ ball p (L * ρ p), P x / ρ x < 3 * Δ / 20) ∨
      (∃ y ∈ ball p (L * ρ p), 3 * Δ / 20 ≤ P y / ρ y) ∧
      ∀ x ∈ ball p (L * ρ p),
        P x / ρ x ∈ Icc (Δ / 10) (181 * Δ / 20) ∧ infDist x E / ρ x < 50 * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hvar (a x : X) (ha : a ∈ ball p (L * ρ p))
      (hx : x ∈ ball p (L * ρ p)) (hv : P a / ρ a ≤ 10 * Δ) :
      |P x / ρ x - P a / ρ a| < Δ / 20 := by
    have hh := slow_scale_quotient_variation hP hρ hK (hpos p) (hpos a) (hpos x)
      hL hsmall hLsmall ha hx (by rw [abs_of_nonneg (div_nonneg (hPnonneg a) (hpos a).le)]; exact hv)
    exact hh.trans_le (by linarith)
  have hupper (x : X) (hx : x ∈ ball p (L * ρ p)) : P x / ρ x ≤ 181 * Δ / 20 := by
    have hh := abs_lt.mp (hvar q x hq hx (by linarith))
    linarith
  by_cases hlow : ∀ x ∈ ball p (L * ρ p), P x / ρ x < 3 * Δ / 20
  · exact Or.inl hlow
  · push Not at hlow
    obtain ⟨y, hy, hyvalue⟩ := hlow
    refine Or.inr ⟨⟨y, hy, hyvalue⟩, ?_⟩
    intro x hx
    have hyupper := hupper y hy
    have hdiff := abs_lt.mp (hvar y x hy hx (by linarith))
    refine ⟨⟨by linarith, hupper x hx⟩, ?_⟩
    have hrholow : 3 / 4 * ρ p ≤ ρ x := by
      have hh := hρ.dist_le_mul x p
      rw [Real.dist_eq] at hh
      have h1 := mul_le_mul_of_nonneg_left hx.le (NNReal.coe_nonneg Λ)
      have h2 := mul_le_mul_of_nonneg_right hLsmall (hpos p).le
      nlinarith [(abs_le.mp hh).1]
    have hd := infDist_le_infDist_add_dist (x := x) (y := p) (s := E)
    change dist x p < L * ρ p at hx
    apply (div_lt_iff₀ (hpos x)).mpr
    have h1 := mul_le_mul_of_nonneg_left hrholow (show 0 ≤ 50 * Δ by positivity)
    have h2 := mul_le_mul_of_nonneg_right hΔ (hpos p).le
    nlinarith [mul_pos hΔ0 (hpos p)]

end GC.MetricGeometry
