import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

theorem lipschitz_quotient_difference_le {P ρ : X → ℝ} {K Λ : NNReal}
    (hP : LipschitzWith K P) (hρ : LipschitzWith Λ ρ) {a x : X}
    (ha : 0 < ρ a) (hx : 0 < ρ x) :
    |P x / ρ x - P a / ρ a| ≤ (K + |P a / ρ a| * Λ) * dist x a / ρ x := by
  have heq : P x / ρ x - P a / ρ a =
      ((P x - P a) + (P a / ρ a) * (ρ a - ρ x)) / ρ x := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hx]
  apply (div_le_div_iff_of_pos_right hx).mpr
  have h1 := hP.dist_le_mul x a
  have h2 := hρ.dist_le_mul a x
  rw [Real.dist_eq] at h1
  rw [Real.dist_eq, dist_comm a x] at h2
  calc
    |(P x - P a) + (P a / ρ a) * (ρ a - ρ x)| ≤
        |P x - P a| + |P a / ρ a| * |ρ a - ρ x| := by
      simpa only [abs_mul] using abs_add_le (P x - P a) ((P a / ρ a) * (ρ a - ρ x))
    _ ≤ K * dist x a + |P a / ρ a| * (Λ * dist x a) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = _ := by ring

theorem slow_scale_quotient_variation {P ρ : X → ℝ} {K Λ : NNReal}
    (hP : LipschitzWith K P) (hρ : LipschitzWith Λ ρ) (hK : (K : ℝ) ≤ 2)
    {p a x : X} (hp : 0 < ρ p) (ha : 0 < ρ a) (hx : 0 < ρ x)
    {L Δ : ℝ} (hL : 0 < L)
    (hsmall : Δ * Λ ≤ 1 / 100) (hLsmall : L * Λ ≤ 1 / 4)
    (haD : a ∈ ball p (L * ρ p)) (hxD : x ∈ ball p (L * ρ p))
    (hvalue : |P a / ρ a| ≤ 10 * Δ) : |P x / ρ x - P a / ρ a| < 6 * L := by
  have hrholow : 3 / 4 * ρ p ≤ ρ x := by
    have hh := hρ.dist_le_mul x p
    rw [Real.dist_eq] at hh
    have hdist : dist x p ≤ L * ρ p := hxD.le
    have h1 := mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg Λ)
    have h2 := mul_le_mul_of_nonneg_right hLsmall hp.le
    nlinarith [(abs_le.mp hh).1]
  have hd : dist x a < 2 * L * ρ p := by
    have ht := dist_triangle x p a
    rw [dist_comm p a] at ht
    change dist a p < L * ρ p at haD
    change dist x p < L * ρ p at hxD
    linarith
  have hcoef : (K : ℝ) + |P a / ρ a| * Λ ≤ 21 / 10 := by
    have hh := mul_le_mul_of_nonneg_right hvalue (NNReal.coe_nonneg Λ)
    nlinarith
  have hbound := lipschitz_quotient_difference_le hP hρ ha hx
  apply hbound.trans_lt
  apply (div_lt_iff₀ hx).mpr
  have h1 := mul_le_mul_of_nonneg_right hcoef (dist_nonneg (x := x) (y := a))
  have h2 := mul_le_mul_of_nonneg_left hrholow (show 0 ≤ 6 * L by positivity)
  nlinarith [mul_pos hL hp]

end GC.MetricGeometry
