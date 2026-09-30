import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace GC.MetricGeometry

private theorem abs_sub_le_of_common_scale {a b R : ℝ}
    (ha : 3 * R / 4 ≤ a ∧ a ≤ 5 * R / 4)
    (hb : 3 * R / 4 ≤ b ∧ b ≤ 5 * R / 4) : |b - a| ≤ 2 * a / 3 := by
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem scale_comparison_of_retained_marker {P X I : Type*}
    (f : P → X) (ρ : P → ℝ) (marker : I → X → ℝ) (R : I → ℝ)
    (hR : ∀ i, 0 < R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {p q : P} (heq : f p = f q) (i : I) (hfull : marker i (f p) = R i) :
    0 < ρ p ∧ (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hp := hsupport i p (by rw [hfull]; exact hR i)
  have hq := hsupport i q (by rw [← heq, hfull]; exact hR i)
  exact ⟨by linarith [hR i], by linarith [hp.1, hp.2, hq.1, hq.2],
    by linarith [hp.1, hp.2, hq.1, hq.2]⟩

theorem radius_control_of_retained_markers {P X I : Type*} [PseudoMetricSpace X]
    (f : P → X) (ρ : P → ℝ) (marker : I → X → ℝ) (R : I → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (p q : P) :
    |σ * ρ q - σ * ρ p| ≤ 2 * (dist (f p) (f q) + σ * ρ p) := by
  obtain ⟨i, hi⟩ := hfull p
  obtain ⟨j, hj⟩ := hfull q
  have hp := hsupport i p (by rw [hi]; exact hR i)
  have hq := hsupport j q (by rw [hj]; exact hR j)
  have hp0 : 0 ≤ ρ p := by linarith [hR i]
  have hq0 : 0 ≤ ρ q := by linarith [hR j]
  have hd : 0 ≤ dist (f p) (f q) := dist_nonneg
  have hmul : 0 ≤ σ * ρ p := mul_nonneg hσ hp0
  rw [← mul_sub, abs_mul, abs_of_nonneg hσ]
  by_cases hlarge : R i ≤ 2 * dist (f p) (f q) ∧ R j ≤ 2 * dist (f p) (f q)
  · have hab : |ρ q - ρ p| ≤ (5 / 2 : ℝ) * dist (f p) (f q) := by
      rw [abs_le]
      constructor <;> linarith [hlarge.1, hlarge.2, hp.2, hq.2]
    have hs := mul_le_mul_of_nonneg_left hab hσ
    have hs' := mul_le_mul_of_nonneg_right hσhalf hd
    nlinarith
  · have hcommon : ∃ k, 3 * R k / 4 ≤ ρ p ∧ ρ p ≤ 5 * R k / 4 ∧
        3 * R k / 4 ≤ ρ q ∧ ρ q ≤ 5 * R k / 4 := by
      by_cases hiR : 2 * dist (f p) (f q) < R i
      · have hm := (hmarker i).dist_le_mul (f p) (f q)
        rw [Real.dist_eq, hi] at hm
        simp only [NNReal.coe_one, one_mul] at hm
        have hpos : 0 < marker i (f q) := by linarith [(abs_le.mp hm).2, hR i]
        have hqi := hsupport i q hpos
        exact ⟨i, hp.1, hp.2, hqi.1, hqi.2⟩
      · have hjR : 2 * dist (f p) (f q) < R j := by
          by_contra hh
          exact hlarge ⟨le_of_not_gt hiR, le_of_not_gt hh⟩
        have hm := (hmarker j).dist_le_mul (f p) (f q)
        rw [Real.dist_eq, hj] at hm
        simp only [NNReal.coe_one, one_mul] at hm
        have hpos : 0 < marker j (f p) := by linarith [(abs_le.mp hm).1, hR j]
        have hpj := hsupport j p hpos
        exact ⟨j, hpj.1, hpj.2, hq.1, hq.2⟩
    obtain ⟨k, hkp, hpk, hkq, hqk⟩ := hcommon
    have ha := abs_sub_le_of_common_scale ⟨hkp, hpk⟩ ⟨hkq, hqk⟩
    have hh := mul_le_mul_of_nonneg_left ha hσ
    nlinarith

theorem scale_bounds_on_closedBall {P : Type*} [PseudoMetricSpace P]
    {ρ : P → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ) {p q : P} {C : ℝ}
    (hp : 0 < ρ p) (hsmall : (Λ : ℝ) * C ≤ 1 / 4)
    (hq : q ∈ Metric.closedBall p (C * ρ p)) :
    3 * ρ p / 4 ≤ ρ q ∧ ρ q ≤ 5 * ρ p / 4 := by
  have hh := hρ.dist_le_mul q p
  rw [Real.dist_eq] at hh
  have hd : dist q p ≤ C * ρ p := hq
  have h1 := mul_le_mul_of_nonneg_left hd Λ.coe_nonneg
  have h2 := mul_le_mul_of_nonneg_right hsmall hp.le
  have hb : |ρ q - ρ p| ≤ ρ p / 4 := by nlinarith
  exact ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩

end GC.MetricGeometry
